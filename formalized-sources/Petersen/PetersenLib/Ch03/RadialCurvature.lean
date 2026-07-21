import PetersenLib.Ch03.DistanceFunctions
import PetersenLib.Ch03.SectionalCurvature

/-!
# Petersen Ch. 3, §3.2.1/§3.2.3–§3.2.5 — The radial curvature equation

The **radial curvature equation** (Theorem 3.2.2) in its three forms — the
`(1,1)`-operator form `(∇_{∇f}S)(X) + S²(X) − ∇_X(S(∇f)) = −R(X,∇f)∇f`, the
`(0,2)`-form via `∇ Hess f`, and the Lie-derivative form via `L_{∇f} Hess f` —
together with its specializations to distance functions: Corollary 3.2.10
(`radialEquation_distanceFunction`, `∇_{∂_r}∂_r = 0` and
`∇_{∂_r}S + S² = −R_{∂_r}`), Proposition 3.2.11
(`distanceFunction_curvatureEquations`, the fundamental equations
`L_{∂_r}g = 2 Hess r`, `∇_{∂_r}Hess r + Hess²r = −R(·,∂_r,∂_r,·)`,
`L_{∂_r}Hess r − Hess²r = −R(·,∂_r,∂_r,·)`), the second-order Jacobi equation
(`jacobiField_secondOrderEquation`, `∇_{∂_r}∇_{∂_r}J = −R(J,∂_r)∂_r`), the
fundamental equations along Jacobi and parallel fields
(`jacobiField_curvatureEquations`, `parallelField_curvatureEquation`), the
sectional-curvature form of the radial curvature term
(`jacobiField_sectionalCurvatureFormula`), and the sign analysis of the
Riccati equation (`externalForceInternalReaction`).

## Design notes

* Following the Ch. 2–3 house style, all statements are pointwise at `p : M`
  in raw section fields with explicit `IsSmoothVectorField` hypotheses; a
  distance function is a globally smooth `r : M → ℝ` satisfying the eikonal
  equation on an open set `U` (`IsDistanceFunction`), and conclusions hold at
  points of `U`.
* The bridge `hessianLieDerivative_eq_metricInner_cov`
  (`Hess f(X,Y) = g(∇_X∇f, Y)`) composes Prop. 2.2.6 with the gradient form of
  `∇df`; everything in this file funnels through it.
* `(∇_N S)(X)` is realized literally as `∇_N(S(X)) − S(∇_N X)`
  (`hessianOperatorCovariantDerivative`), which coincides definitionally with
  the second covariant derivative `∇²_{N,X}∇f` (`secondCovariantDerivativeField`);
  the operator form of the radial curvature equation is then a rearrangement
  of the Ricci identity `R(X,Y)Z = ∇²_{X,Y}Z − ∇²_{Y,X}Z`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.2.1, §3.2.3–§3.2.6.
-/

open Bundle Set Function Filter
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Bridges between the Hessian `(0,2)`-tensor and the Hessian operator -/

section Bridges

variable [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace E]

/-- Two-slot update, first slot: `(![X, Y])[0 ↦ Z] = ![Z, Y]`. -/
private theorem update_pair_fst {α : Type*} (X Y Z : α) :
    Function.update ![X, Y] (0 : Fin 2) Z = ![Z, Y] := by
  funext j
  fin_cases j
  · simp
  · simp

/-- Two-slot update, second slot: `(![X, Y])[1 ↦ Z] = ![X, Z]`. -/
private theorem update_pair_snd {α : Type*} (X Y Z : α) :
    Function.update ![X, Y] (1 : Fin 2) Z = ![X, Z] := by
  funext j
  fin_cases j
  · simp
  · simp

/-- **Eng.** The workhorse bridge: `Hess f(X, Y) = g(∇_X ∇f, Y)` pointwise, for
smooth `X`, `Y` and smooth gradient — Prop. 2.2.6 composed with the gradient
form of `∇df`. -/
theorem hessianLieDerivative_eq_metricInner_cov {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hgradf : IsSmoothVectorField (gradient g f)) (p : M) :
    hessianLieDerivative g f ![X, Y] p
      = g.metricInner p (D.cov p (X p) (gradient g f)) (Y p) :=
  (hessian_via_covariantDerivative D hf hX hY hgradf p).symm.trans
    (covariantDerivative_differential_eq_gradient D X Y hY hgradf p)

/-- Symmetry of the Hessian `(0,2)`-tensor on smooth fields. -/
theorem hessianLieDerivative_symm {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hgradf : IsSmoothVectorField (gradient g f)) (p : M) :
    hessianLieDerivative g f ![X, Y] p = hessianLieDerivative g f ![Y, X] p := by
  rw [← hessian_via_covariantDerivative D hf hX hY hgradf p,
    ← hessian_via_covariantDerivative D hf hY hX hgradf p,
    covariantDerivative_differential_symm D hf hX hY p]

/-- **Eng.** `Hess²f(X, Y) = g(∇_X∇f, ∇_Y∇f)`: the squared Hessian pairs the
Hessian operator against itself, by self-adjointness of `S` (symmetry of the
Hessian). -/
theorem hessianOperatorSquared_eq_metricInner {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hgradf : IsSmoothVectorField (gradient g f)) (p : M) :
    hessianOperatorSquared D.toAffineConnection g f p (X p) (Y p)
      = g.metricInner p (D.cov p (X p) (gradient g f))
          (D.cov p (Y p) (gradient g f)) := by
  have hSX : IsSmoothVectorField
      (D.toAffineConnection.covField X (gradient g f)) := D.smooth_cov hX hgradf
  -- `Hess²f(X,Y) = g(∇_{S(X)}∇f, Y) = Hess f(S(X), Y)`
  have h₁ : hessianOperatorSquared D.toAffineConnection g f p (X p) (Y p)
      = hessianLieDerivative g f
          ![D.toAffineConnection.covField X (gradient g f), Y] p :=
    (hessianLieDerivative_eq_metricInner_cov D hf hSX hY hgradf p).symm
  -- `Hess f(S(X), Y) = Hess f(Y, S(X)) = g(∇_Y∇f, S(X)) = g(S(X), ∇_Y∇f)`
  rw [h₁, hessianLieDerivative_symm D hf hSX hY hgradf p,
    hessianLieDerivative_eq_metricInner_cov D hf hY hSX hgradf p]
  exact g.metricInner_comm ..

end Bridges

/-! ## The gradient of `½|∇f|²` -/

section GradientNormSq

variable [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M]

omit [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- The squared gradient length `|∇f|² = g(∇f, ∇f)` is smooth for a smooth
gradient. -/
theorem contMDiff_metricInner_gradient_self {g : RiemannianMetric I M}
    {f : M → ℝ} (hgradf : IsSmoothVectorField (gradient g f)) :
    ContMDiff I 𝓘(ℝ) ∞
      (fun q => g.metricInner q (gradient g f q) (gradient g f q)) := by
  have h := (metricOperator_isTensorOperator g).smooth_eval
    ![gradient g f, gradient g f]
    (by intro i; fin_cases i <;> simpa using hgradf)
  have e : (metricOperator g ![gradient g f, gradient g f] : M → ℝ)
      = fun q => g.metricInner q (gradient g f q) (gradient g f q) := by
    funext q; simp [metricOperator]
  rwa [e] at h

/-- **Math.** `∇(½|∇f|²) = ∇_{∇f}∇f = S(∇f)` (Petersen §3.2.1, used in the
second form of Theorem 3.2.2): the gradient of half the squared gradient
length is the Hessian operator applied to the gradient — by symmetry of the
Hessian and metric compatibility. -/
theorem gradient_half_normSq {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hgradf : IsSmoothVectorField (gradient g f)) :
    gradient g
        (fun q => (1 / 2 : ℝ) * g.metricInner q (gradient g f q) (gradient g f q))
      = D.toAffineConnection.covField (gradient g f) (gradient g f) := by
  funext p
  refine (gradient_unique g _ p _ fun w => ?_).symm
  -- extend `w` to a smooth field `W`
  set W := extendTangentVector p w with hW
  have hWs : IsSmoothVectorField (⇑W) := W.smooth
  have hWp : W p = w := extendTangentVector_apply p w
  -- `g(∇_{∇f}∇f, w) = Hess f(∇f, W) = Hess f(W, ∇f) = g(∇_W∇f, ∇f)`
  have h₁ : g.metricInner p
        (D.toAffineConnection.covField (gradient g f) (gradient g f) p) (W p)
      = g.metricInner p (D.cov p (W p) (gradient g f)) (gradient g f p) := by
    rw [AffineConnection.covField_apply,
      ← hessianLieDerivative_eq_metricInner_cov D hf hgradf hWs hgradf p,
      hessianLieDerivative_symm D hf hgradf hWs hgradf p,
      hessianLieDerivative_eq_metricInner_cov D hf hWs hgradf hgradf p]
  -- metric compatibility: `D_W|∇f|² = 2 g(∇_W∇f, ∇f)`
  have hcompat := D.metric_compat hgradf hgradf p (W p)
  rw [dirTangent_eq_directionalDerivative] at hcompat
  -- differentiability of `|∇f|²`
  have hF : ContMDiff I 𝓘(ℝ) ∞
      (fun q => g.metricInner q (gradient g f q) (gradient g f q)) :=
    contMDiff_metricInner_gradient_self hgradf
  -- assemble: `mfderiv (½|∇f|²) p w = ½ · D_W|∇f|² = g(∇_W∇f, ∇f) = g(∇_{∇f}∇f, w)`
  have hdd : directionalDerivative (⇑W)
        (fun q => (1 / 2 : ℝ)
          * g.metricInner q (gradient g f q) (gradient g f q)) p
      = (1 / 2 : ℝ) * directionalDerivative (⇑W)
          (fun q => g.metricInner q (gradient g f q) (gradient g f q)) p :=
    directionalDerivative_const_smul ((hF p).mdifferentiableAt (by simp))
      (1 / 2 : ℝ) (⇑W)
  have hmf : mfderiv I 𝓘(ℝ)
        (fun q => (1 / 2 : ℝ)
          * g.metricInner q (gradient g f q) (gradient g f q)) p w
      = directionalDerivative (⇑W)
          (fun q => (1 / 2 : ℝ)
            * g.metricInner q (gradient g f q) (gradient g f q)) p := by
    rw [directionalDerivative_apply, hWp]
  have hcomm : g.metricInner p (gradient g f p) (D.cov p (W p) (gradient g f))
      = g.metricInner p (D.cov p (W p) (gradient g f)) (gradient g f p) :=
    g.metricInner_comm ..
  rw [hmf, hdd, hcompat, hcomm, ← hWp, h₁]
  ring

end GradientNormSq

/-! ## The covariant derivative of the Hessian operator -/

section HessianOperatorDerivative

variable [FiniteDimensional ℝ E]

/-- **Math.** The **covariant derivative of the Hessian operator** `S = ∇∇f`
(Petersen §3.2.1): the `(1,1)`-tensor `(∇_N S)(X) = ∇_N(S(X)) − S(∇_N X)`,
given by the Leibniz rule. It coincides with the second covariant derivative
`∇²_{N,X}∇f` (`hessianOperatorCovariantDerivative_eq_secondCovariantDerivative`). -/
def hessianOperatorCovariantDerivative (D : AffineConnection I M)
    (g : RiemannianMetric I M) (f : M → ℝ) (N X : Π x : M, TangentSpace I x)
    (p : M) : TangentSpace I p :=
  D.cov p (N p) (fun q => hessianOperator D g f q (X q))
    - hessianOperator D g f p (D.cov p (N p) X)

theorem hessianOperatorCovariantDerivative_apply (D : AffineConnection I M)
    (g : RiemannianMetric I M) (f : M → ℝ) (N X : Π x : M, TangentSpace I x)
    (p : M) :
    hessianOperatorCovariantDerivative D g f N X p
      = D.cov p (N p) (fun q => hessianOperator D g f q (X q))
        - hessianOperator D g f p (D.cov p (N p) X) := rfl

/-- `(∇_N S)(X) = ∇²_{N,X}∇f`: the covariant derivative of the Hessian
operator is the second covariant derivative of the gradient. -/
theorem hessianOperatorCovariantDerivative_eq_secondCovariantDerivative
    (D : AffineConnection I M) (g : RiemannianMetric I M) (f : M → ℝ)
    (N X : Π x : M, TangentSpace I x) (p : M) :
    hessianOperatorCovariantDerivative D g f N X p
      = secondCovariantDerivativeField D N X (gradient g f) p := rfl

end HessianOperatorDerivative

/-! ## `∇ Hess f` and `L Hess f` against the Hessian operator -/

section HessianTensorDerivatives

variable [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace E]

/-- **Eng.** Covariant differentiation commutes with the type change from
`(1,1)`- to `(0,2)`-tensors: `(∇_N Hess f)(X, Y) = g(∇²_{N,X}∇f, Y)
= g((∇_N S)(X), Y)`. -/
theorem covariantDerivativeTensor_hessian_eq_metricInner
    {g : RiemannianMetric I M} (D : RiemannianConnection I g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {N X Y : Π x : M, TangentSpace I x}
    (hN : IsSmoothVectorField N) (hX : IsSmoothVectorField X)
    (hY : IsSmoothVectorField Y)
    (hgradf : IsSmoothVectorField (gradient g f)) (p : M) :
    covariantDerivativeTensor D.toAffineConnection N (hessianLieDerivative g f)
        ![X, Y] p
      = g.metricInner p
          (secondCovariantDerivativeField D.toAffineConnection N X
            (gradient g f) p) (Y p) := by
  have hSX : IsSmoothVectorField
      (D.toAffineConnection.covField X (gradient g f)) := D.smooth_cov hX hgradf
  have hNX : IsSmoothVectorField (D.toAffineConnection.covField N X) :=
    D.smooth_cov hN hX
  have hNY : IsSmoothVectorField (D.toAffineConnection.covField N Y) :=
    D.smooth_cov hN hY
  -- the Hessian as a function is `q ↦ g(∇_X∇f, Y)(q)`
  have hfun : (hessianLieDerivative g f ![X, Y] : M → ℝ)
      = fun q => g.metricInner q
          (D.toAffineConnection.covField X (gradient g f) q) (Y q) := by
    funext q
    rw [hessianLieDerivative_eq_metricInner_cov D hf hX hY hgradf q]
    rfl
  -- metric compatibility along `N` on the pair `(∇_X∇f, Y)`
  have hcompat := D.metric_compat hSX hY p (N p)
  rw [dirTangent_eq_directionalDerivative] at hcompat
  -- expand the covariant derivative of the `(0,2)`-tensor
  rw [covariantDerivativeTensor_formula, Fin.sum_univ_two,
    update_pair_fst, update_pair_snd]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hfun]
  have hupdfst : hessianLieDerivative g f
        ![D.toAffineConnection.covField N X, Y] p
      = g.metricInner p
          (D.cov p (D.toAffineConnection.covField N X p) (gradient g f)) (Y p) :=
    hessianLieDerivative_eq_metricInner_cov D hf hNX hY hgradf p
  have hupdsnd : hessianLieDerivative g f
        ![X, D.toAffineConnection.covField N Y] p
      = g.metricInner p (D.cov p (X p) (gradient g f))
          (D.toAffineConnection.covField N Y p) :=
    hessianLieDerivative_eq_metricInner_cov D hf hX hNY hgradf p
  rw [hupdfst, hupdsnd, hcompat, secondCovariantDerivativeField_apply,
    g.metricInner_sub_left]
  simp only [AffineConnection.covField_apply]
  ring

/-- **Eng.** The Lie and covariant derivatives of `Hess f` along `∇f` differ by
twice the squared Hessian: `(L_{∇f} Hess f)(X,Y) = (∇_{∇f} Hess f)(X,Y)
+ 2 Hess²f(X,Y)` — torsion-freeness converts each Lie-bracket correction into
a covariant one at the cost of one `S`, and self-adjointness of `S` collects
both into `Hess²f`. -/
theorem lieDerivativeTensor_hessian_eq_covariant
    {g : RiemannianMetric I M} (D : RiemannianConnection I g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hgradf : IsSmoothVectorField (gradient g f)) (p : M) :
    lieDerivativeTensor I (gradient g f) (hessianLieDerivative g f) ![X, Y] p
      = covariantDerivativeTensor D.toAffineConnection (gradient g f)
          (hessianLieDerivative g f) ![X, Y] p
        + 2 * hessianOperatorSquared D.toAffineConnection g f p (X p) (Y p) := by
  have hLX : IsSmoothVectorField (lieDerivativeVectorField I (gradient g f) X) :=
    hgradf.lieDerivativeVectorField hX
  have hLY : IsSmoothVectorField (lieDerivativeVectorField I (gradient g f) Y) :=
    hgradf.lieDerivativeVectorField hY
  have hNX : IsSmoothVectorField
      (D.toAffineConnection.covField (gradient g f) X) := D.smooth_cov hgradf hX
  have hNY : IsSmoothVectorField
      (D.toAffineConnection.covField (gradient g f) Y) := D.smooth_cov hgradf hY
  -- expand both derivative formulas
  rw [lieDerivativeTensor_formula, covariantDerivativeTensor_formula,
    Fin.sum_univ_two, Fin.sum_univ_two, update_pair_fst, update_pair_snd,
    update_pair_fst, update_pair_snd]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  -- bridge each of the four correction terms
  have hb₁ : hessianLieDerivative g f
        ![lieDerivativeVectorField I (gradient g f) X, Y] p
      = g.metricInner p
          (D.cov p (lieDerivativeVectorField I (gradient g f) X p)
            (gradient g f)) (Y p) :=
    hessianLieDerivative_eq_metricInner_cov D hf hLX hY hgradf p
  have hb₂ : hessianLieDerivative g f
        ![X, lieDerivativeVectorField I (gradient g f) Y] p
      = g.metricInner p (D.cov p (X p) (gradient g f))
          (lieDerivativeVectorField I (gradient g f) Y p) :=
    hessianLieDerivative_eq_metricInner_cov D hf hX hLY hgradf p
  have hb₃ : hessianLieDerivative g f
        ![D.toAffineConnection.covField (gradient g f) X, Y] p
      = g.metricInner p
          (D.cov p (D.toAffineConnection.covField (gradient g f) X p)
            (gradient g f)) (Y p) :=
    hessianLieDerivative_eq_metricInner_cov D hf hNX hY hgradf p
  have hb₄ : hessianLieDerivative g f
        ![X, D.toAffineConnection.covField (gradient g f) Y] p
      = g.metricInner p (D.cov p (X p) (gradient g f))
          (D.toAffineConnection.covField (gradient g f) Y p) :=
    hessianLieDerivative_eq_metricInner_cov D hf hX hNY hgradf p
  rw [hb₁, hb₂, hb₃, hb₄]
  -- torsion-freeness: `∇_{∇f}X − ∇_X∇f = [∇f, X]`
  have htfX := D.torsion_free hgradf hX p
  have htfY := D.torsion_free hgradf hY p
  -- first-slot difference: `g(∇_{∇_{∇f}X − [∇f,X]}∇f, Y) = g(∇_{S(X)}∇f, Y) = Hess²f(X,Y)`
  have hdiff₁ : g.metricInner p
        (D.cov p (D.toAffineConnection.covField (gradient g f) X p)
          (gradient g f)) (Y p)
      - g.metricInner p
          (D.cov p (lieDerivativeVectorField I (gradient g f) X p)
            (gradient g f)) (Y p)
      = hessianOperatorSquared D.toAffineConnection g f p (X p) (Y p) := by
    rw [← g.metricInner_sub_left, ← D.toAffineConnection.cov_sub_direction]
    have hdir : D.toAffineConnection.covField (gradient g f) X p
          - lieDerivativeVectorField I (gradient g f) X p
        = D.cov p (X p) (gradient g f) := by
      rw [AffineConnection.covField_apply, ← htfX]
      module
    rw [hdir]
    rfl
  -- second-slot difference: `g(S(X), S(Y)) = Hess²f(X,Y)`
  have hdiff₂ : g.metricInner p (D.cov p (X p) (gradient g f))
        (D.toAffineConnection.covField (gradient g f) Y p)
      - g.metricInner p (D.cov p (X p) (gradient g f))
          (lieDerivativeVectorField I (gradient g f) Y p)
      = hessianOperatorSquared D.toAffineConnection g f p (X p) (Y p) := by
    rw [← g.metricInner_sub_right]
    have hdir : D.toAffineConnection.covField (gradient g f) Y p
          - lieDerivativeVectorField I (gradient g f) Y p
        = D.cov p (Y p) (gradient g f) := by
      rw [AffineConnection.covField_apply, ← htfY]
      module
    rw [hdir, hessianOperatorSquared_eq_metricInner D hf hX hY hgradf p]
  linarith [hdiff₁, hdiff₂]

end HessianTensorDerivatives

/-! ## Theorem 3.2.2 — the radial curvature equation -/

section RadialCurvatureEquation

variable [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **The radial curvature equation** (Petersen Theorem 3.2.2,
`thm:pet-ch3-radial-curvature-equation`), in its three forms: for a smooth
function `f` with smooth gradient and smooth fields `X, Y`,

1. `(∇_{∇f}S)(X) + S²(X) − ∇_X(S(∇f)) = −R(X,∇f)∇f` (operator form);
2. `(∇_{∇f}Hess f)(X,Y) + Hess²f(X,Y) − Hess(½|∇f|²)(X,Y) = −R(X,∇f,∇f,Y)`;
3. `(L_{∇f}Hess f)(X,Y) − Hess²f(X,Y) − Hess(½|∇f|²)(X,Y) = −R(X,∇f,∇f,Y)`.

The operator form is a rearrangement of the Ricci identity
`R(X,∇f)∇f = ∇²_{X,∇f}∇f − ∇²_{∇f,X}∇f`; the second form is its metric
pairing, and the third follows since `L` and `∇` of `Hess f` along `∇f`
differ by `2 Hess²f`. -/
theorem radialCurvatureEquation {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hgradf : IsSmoothVectorField (gradient g f)) (p : M) :
    hessianOperatorCovariantDerivative D.toAffineConnection g f
          (gradient g f) X p
        + hessianOperator D.toAffineConnection g f p
            (hessianOperator D.toAffineConnection g f p (X p))
        - D.cov p (X p)
            (D.toAffineConnection.covField (gradient g f) (gradient g f))
      = -curvatureTensor D.toAffineConnection X (gradient g f) (gradient g f) p
    ∧ covariantDerivativeTensor D.toAffineConnection (gradient g f)
          (hessianLieDerivative g f) ![X, Y] p
        + hessianOperatorSquared D.toAffineConnection g f p (X p) (Y p)
        - hessianLieDerivative g
            (fun q => (1 / 2 : ℝ)
              * g.metricInner q (gradient g f q) (gradient g f q)) ![X, Y] p
      = -curvatureTensorFour D X (gradient g f) (gradient g f) Y p
    ∧ lieDerivativeTensor I (gradient g f) (hessianLieDerivative g f) ![X, Y] p
        - hessianOperatorSquared D.toAffineConnection g f p (X p) (Y p)
        - hessianLieDerivative g
            (fun q => (1 / 2 : ℝ)
              * g.metricInner q (gradient g f q) (gradient g f q)) ![X, Y] p
      = -curvatureTensorFour D X (gradient g f) (gradient g f) Y p := by
  -- the operator form: a rearrangement of the Ricci identity
  have hricci := curvatureTensor_eq_ricci_identity D hX hgradf (gradient g f) p
  rw [secondCovariantDerivativeField_apply, secondCovariantDerivativeField_apply]
    at hricci
  have hform₁ : hessianOperatorCovariantDerivative D.toAffineConnection g f
          (gradient g f) X p
        + hessianOperator D.toAffineConnection g f p
            (hessianOperator D.toAffineConnection g f p (X p))
        - D.cov p (X p)
            (D.toAffineConnection.covField (gradient g f) (gradient g f))
      = -curvatureTensor D.toAffineConnection X (gradient g f)
          (gradient g f) p := by
    rw [hessianOperatorCovariantDerivative_eq_secondCovariantDerivative,
      secondCovariantDerivativeField_apply]
    have hsq : hessianOperator D.toAffineConnection g f p
        (hessianOperator D.toAffineConnection g f p (X p))
        = D.cov p (D.cov p (X p) (gradient g f)) (gradient g f) := rfl
    rw [hsq]
    simp only [AffineConnection.covField_apply] at hricci ⊢
    linear_combination (norm := module) hricci
  refine ⟨hform₁, ?_, ?_⟩
  -- the `(0,2)`-form: pair the operator form with `g(−, Y)`
  · -- the gradient of `½|∇f|²`
    have hgradsq := gradient_half_normSq D hf hgradf
    have hgradsq_smooth : IsSmoothVectorField (gradient g
        (fun q => (1 / 2 : ℝ)
          * g.metricInner q (gradient g f q) (gradient g f q))) := by
      rw [hgradsq]
      exact D.smooth_cov hgradf hgradf
    have hsq_smooth : ContMDiff I 𝓘(ℝ) ∞
        (fun q => (1 / 2 : ℝ)
          * g.metricInner q (gradient g f q) (gradient g f q)) := by
      simpa [smul_eq_mul] using
        (contMDiff_const (I := I) (I' := 𝓘(ℝ, ℝ)) (c := (1 / 2 : ℝ))).smul
          (contMDiff_metricInner_gradient_self hgradf)
    -- `Hess(½|∇f|²)(X,Y) = g(∇_X(S(∇f)), Y)`
    have hthird : hessianLieDerivative g
          (fun q => (1 / 2 : ℝ)
            * g.metricInner q (gradient g f q) (gradient g f q)) ![X, Y] p
        = g.metricInner p
            (D.cov p (X p)
              (D.toAffineConnection.covField (gradient g f) (gradient g f)))
            (Y p) := by
      rw [hessianLieDerivative_eq_metricInner_cov D hsq_smooth hX hY
        hgradsq_smooth p, hgradsq]
    -- pair the operator form with `Y`
    have hpair := congrArg (fun v => g.metricInner p v (Y p)) hform₁
    simp only [g.metricInner_sub_left, g.metricInner_add_left,
      g.metricInner_neg_left] at hpair
    rw [covariantDerivativeTensor_hessian_eq_metricInner D hf hgradf hX hY
      hgradf p, ← hessianOperatorCovariantDerivative_eq_secondCovariantDerivative,
      hthird, curvatureTensorFour_apply]
    have hsq : hessianOperatorSquared D.toAffineConnection g f p (X p) (Y p)
        = g.metricInner p
            (hessianOperator D.toAffineConnection g f p
              (hessianOperator D.toAffineConnection g f p (X p))) (Y p) := rfl
    rw [hsq]
    linarith [hpair]
  -- the Lie form: substitute `L = ∇ + 2 Hess²`
  · have hgradsq := gradient_half_normSq D hf hgradf
    have hgradsq_smooth : IsSmoothVectorField (gradient g
        (fun q => (1 / 2 : ℝ)
          * g.metricInner q (gradient g f q) (gradient g f q))) := by
      rw [hgradsq]
      exact D.smooth_cov hgradf hgradf
    have hsq_smooth : ContMDiff I 𝓘(ℝ) ∞
        (fun q => (1 / 2 : ℝ)
          * g.metricInner q (gradient g f q) (gradient g f q)) := by
      simpa [smul_eq_mul] using
        (contMDiff_const (I := I) (I' := 𝓘(ℝ, ℝ)) (c := (1 / 2 : ℝ))).smul
          (contMDiff_metricInner_gradient_self hgradf)
    have hthird : hessianLieDerivative g
          (fun q => (1 / 2 : ℝ)
            * g.metricInner q (gradient g f q) (gradient g f q)) ![X, Y] p
        = g.metricInner p
            (D.cov p (X p)
              (D.toAffineConnection.covField (gradient g f) (gradient g f)))
            (Y p) := by
      rw [hessianLieDerivative_eq_metricInner_cov D hsq_smooth hX hY
        hgradsq_smooth p, hgradsq]
    have hpair := congrArg (fun v => g.metricInner p v (Y p)) hform₁
    simp only [g.metricInner_sub_left, g.metricInner_add_left,
      g.metricInner_neg_left] at hpair
    rw [lieDerivativeTensor_hessian_eq_covariant D hf hX hY hgradf p,
      covariantDerivativeTensor_hessian_eq_metricInner D hf hgradf hX hY
      hgradf p, ← hessianOperatorCovariantDerivative_eq_secondCovariantDerivative,
      hthird, curvatureTensorFour_apply]
    have hsq : hessianOperatorSquared D.toAffineConnection g f p (X p) (Y p)
        = g.metricInner p
            (hessianOperator D.toAffineConnection g f p
              (hessianOperator D.toAffineConnection g f p (X p))) (Y p) := rfl
    rw [hsq]
    linarith [hpair]

/-- **Math.** The **Lie derivative of the Hessian operator** `S = ∇∇f` along a
field `N` (Petersen §3.2.1, used in Exercise 3.4.3, `rem:pet-ch3-ex-3`): the
`(1,1)`-tensor `(L_N S)(X) = L_N(S(X)) − S(L_N X)`, the Lie-bracket analogue of
`hessianOperatorCovariantDerivative`. -/
def hessianOperatorLieDerivative (D : AffineConnection I M)
    (g : RiemannianMetric I M) (f : M → ℝ) (N X : Π x : M, TangentSpace I x)
    (p : M) : TangentSpace I p :=
  lieDerivativeVectorField I N (fun q => hessianOperator D g f q (X q)) p
    - hessianOperator D g f p (lieDerivativeVectorField I N X p)

omit [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem hessianOperatorLieDerivative_apply (D : AffineConnection I M)
    (g : RiemannianMetric I M) (f : M → ℝ) (N X : Π x : M, TangentSpace I x)
    (p : M) :
    hessianOperatorLieDerivative D g f N X p
      = lieDerivativeVectorField I N (fun q => hessianOperator D g f q (X q)) p
        - hessianOperator D g f p (lieDerivativeVectorField I N X p) := rfl

/-- **Math.** **Exercise 3.4.3** (Petersen, `rem:pet-ch3-ex-3`): for `f` with
Hessian operator `S(X) = ∇_X∇f`,

1. `L_{∇f}S = ∇_{∇f}S` (the Lie and covariant derivatives of `S` along `∇f`
   coincide);
2. `(L_{∇f}S)(X) + S²(X) − ∇_X(S(∇f)) = −R(X,∇f)∇f`, the operator form of the
   radial curvature equation (`thm:pet-ch3-radial-curvature-equation`) with
   `∇_{∇f}S` replaced by `L_{∇f}S`;
3. reconciliation with the `(0,2)`-Hessian form of the same theorem: pairing
   `L_{∇f}S` with the metric against `Y` recovers the `(0,2)`-tensor
   `∇_{∇f}Hess f` used there.

Part 1 is a torsion-freeness computation: `L_{∇f}(S(X)) − S(L_{∇f}X)` and
`∇_{∇f}(S(X)) − S(∇_{∇f}X)` differ by `∇_{S(X)}∇f − S(∇_X∇f) = S²(X) − S²(X)
= 0`, using `∇_{∇f}Y − ∇_Y∇f = L_{∇f}Y` for `Y = X` and `Y = S(X)`. Part 2 is
`radialCurvatureEquation` composed with part 1; part 3 is
`covariantDerivativeTensor_hessian_eq_metricInner` composed with part 1. -/
theorem exercise3_4_3 {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hgradf : IsSmoothVectorField (gradient g f)) (p : M) :
    hessianOperatorLieDerivative D.toAffineConnection g f (gradient g f) X p
      = hessianOperatorCovariantDerivative D.toAffineConnection g f
          (gradient g f) X p
    ∧ hessianOperatorLieDerivative D.toAffineConnection g f (gradient g f) X p
        + hessianOperator D.toAffineConnection g f p
            (hessianOperator D.toAffineConnection g f p (X p))
        - D.cov p (X p)
            (D.toAffineConnection.covField (gradient g f) (gradient g f))
      = -curvatureTensor D.toAffineConnection X (gradient g f) (gradient g f) p
    ∧ covariantDerivativeTensor D.toAffineConnection (gradient g f)
          (hessianLieDerivative g f) ![X, Y] p
      = g.metricInner p
          (hessianOperatorLieDerivative D.toAffineConnection g f
            (gradient g f) X p) (Y p) := by
  have hSX : IsSmoothVectorField
      (fun q => hessianOperator D.toAffineConnection g f q (X q)) :=
    D.smooth_cov hX hgradf
  have hpart1 : hessianOperatorLieDerivative D.toAffineConnection g f
        (gradient g f) X p
      = hessianOperatorCovariantDerivative D.toAffineConnection g f
          (gradient g f) X p := by
    have htf1 := D.torsion_free hgradf hSX p
    have htf2 := D.torsion_free hgradf hX p
    have hlin : hessianOperator D.toAffineConnection g f p
          (D.cov p (gradient g f p) X - D.cov p (X p) (gradient g f))
        = hessianOperator D.toAffineConnection g f p
            (D.cov p (gradient g f p) X)
          - hessianOperator D.toAffineConnection g f p
              (D.cov p (X p) (gradient g f)) := by
      simp only [hessianOperator_apply]
      exact D.toAffineConnection.cov_sub_direction p _ _ (gradient g f)
    have e1 : hessianOperator D.toAffineConnection g f p
          (D.cov p (X p) (gradient g f))
        = hessianOperator D.toAffineConnection g f p
            (hessianOperator D.toAffineConnection g f p (X p)) := rfl
    have e2 : D.cov p (hessianOperator D.toAffineConnection g f p (X p))
          (gradient g f)
        = hessianOperator D.toAffineConnection g f p
            (hessianOperator D.toAffineConnection g f p (X p)) := rfl
    rw [hessianOperatorLieDerivative_apply, hessianOperatorCovariantDerivative_apply,
      ← htf1, ← htf2, hlin, e1, e2]
    abel
  refine ⟨hpart1, ?_, ?_⟩
  · rw [hpart1]
    exact (radialCurvatureEquation D hf hX hY hgradf p).1
  · rw [hpart1, hessianOperatorCovariantDerivative_eq_secondCovariantDerivative]
    exact covariantDerivativeTensor_hessian_eq_metricInner D hf hgradf hX hY
      hgradf p

end RadialCurvatureEquation

/-! ## Remark 3.2.3 — tangential/normal decomposition -/

section TangentialNormal

/-- **Math.** The **tangential/normal decomposition** with respect to a unit
normal field `N` (Petersen Remark 3.2.3,
`rem:pet-ch3-tangential-normal-decomposition`):
`X = X^⊤ + X^⊥ = (X − g(X,N)N) + g(X,N)N`. The pair `(X^⊤, X^⊥)` is returned;
`tangentialNormalDecomposition_add` and
`tangentialNormalDecomposition_orthogonal` record that the two parts sum to
`X` and that `X^⊤ ⊥ N` where `N` has unit length. -/
def tangentialNormalDecomposition (g : RiemannianMetric I M)
    (N X : Π x : M, TangentSpace I x) :
    (Π x : M, TangentSpace I x) × (Π x : M, TangentSpace I x) :=
  (fun q => X q - g.metricInner q (X q) (N q) • N q,
    fun q => g.metricInner q (X q) (N q) • N q)

/-- The two parts of the tangential/normal decomposition sum to `X`. -/
theorem tangentialNormalDecomposition_add (g : RiemannianMetric I M)
    (N X : Π x : M, TangentSpace I x) (q : M) :
    (tangentialNormalDecomposition g N X).1 q
        + (tangentialNormalDecomposition g N X).2 q = X q := by
  simp [tangentialNormalDecomposition]

/-- The tangential part is orthogonal to a unit normal `N`. -/
theorem tangentialNormalDecomposition_orthogonal (g : RiemannianMetric I M)
    (N X : Π x : M, TangentSpace I x) (q : M)
    (hN : g.metricInner q (N q) (N q) = 1) :
    g.metricInner q ((tangentialNormalDecomposition g N X).1 q) (N q) = 0 := by
  simp only [tangentialNormalDecomposition]
  rw [g.metricInner_sub_left, g.metricInner_smul_left, hN]
  ring

/-- The normal part is proportional to `N` with coefficient `g(X, N)`. -/
theorem tangentialNormalDecomposition_normal (g : RiemannianMetric I M)
    (N X : Π x : M, TangentSpace I x) (q : M) :
    (tangentialNormalDecomposition g N X).2 q
      = g.metricInner q (X q) (N q) • N q := rfl

end TangentialNormal

/-! ## Corollary 3.2.10 — the radial curvature equation for distance functions -/

section DistanceFunctionEquations

variable [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

omit [LocallyCompactSpace M] in
/-- **Eng.** For a distance function `r` on the open set `U`, the radial field
is geodesic on `U`: `∇_{∂_r}∂_r = 0` at every point of `U` — part (3) of
Proposition 3.2.1 applied to `f = r`, using that `|∇r|² ≡ 1` has vanishing
derivative on the open set `U`. -/
theorem covField_gradient_self_eqOn_zero {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {U : Set M} (hU : IsOpen U) {r : M → ℝ}
    (hr : IsDistanceFunction g U r) (hrs : ContMDiff I 𝓘(ℝ) ∞ r)
    (hgradr : IsSmoothVectorField (gradient g r)) :
    ∀ q ∈ U, D.cov q (gradient g r q) (gradient g r) = 0 := by
  intro q hq
  -- it suffices to pair against every tangent vector
  refine (g.metricInner_eq_iff_eq q _ 0).mp fun Z => ?_
  rw [g.metricInner_zero_left]
  -- extend `Z` to a smooth field
  set W := extendTangentVector q Z with hWdef
  have hWs : IsSmoothVectorField (⇑W) := W.smooth
  have hWq : W q = Z := extendTangentVector_apply q Z
  -- `g(∇_{∂_r}∂_r, Z) = Hess r(∂_r, W) = Hess r(W, ∂_r) = ½ D_W|∇r|²`
  have hsymm : g.metricInner q (D.cov q (gradient g r q) (gradient g r)) (W q)
      = g.metricInner q (D.cov q (W q) (gradient g r)) (gradient g r q) := by
    rw [← hessianLieDerivative_eq_metricInner_cov D hrs hgradr hWs hgradr q,
      hessianLieDerivative_symm D hrs hgradr hWs hgradr q,
      hessianLieDerivative_eq_metricInner_cov D hrs hWs hgradr hgradr q]
  -- metric compatibility along `W`
  have hcompat := D.metric_compat hgradr hgradr q (W q)
  rw [dirTangent_eq_directionalDerivative] at hcompat
  -- `|∇r|² ≡ 1` near `q`, so its derivative vanishes
  have hloc : (fun x => g.metricInner x (gradient g r x) (gradient g r x))
      =ᶠ[𝓝 q] fun _ => (1 : ℝ) := by
    filter_upwards [hU.mem_nhds hq] with x hx
    exact hr.2 x hx
  have hdd : directionalDerivative (⇑W)
      (fun x => g.metricInner x (gradient g r x) (gradient g r x)) q = 0 := by
    rw [directionalDerivative_apply, hloc.mfderiv_eq, mfderiv_const]
    rfl
  rw [hdd] at hcompat
  have hcomm : g.metricInner q (gradient g r q) (D.cov q (W q) (gradient g r))
      = g.metricInner q (D.cov q (W q) (gradient g r)) (gradient g r q) :=
    g.metricInner_comm ..
  rw [← hWq, hsymm]
  linarith [hcompat, hcomm]

/-- **Math.** **Corollary 3.2.10** (Petersen,
`cor:pet-ch3-radial-equation-distance-function`): for a distance function
`r : U → ℝ`, the radial field is geodesic, `∇_{∂_r}∂_r = 0` on `U`, and the
radial curvature equation collapses to
`(∇_{∂_r}S)(X) + S²(X) = −R(X,∂_r)∂_r = −R_{∂_r}(X)`. -/
theorem radialEquation_distanceFunction {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {U : Set M} (hU : IsOpen U) {r : M → ℝ}
    (hr : IsDistanceFunction g U r) (hrs : ContMDiff I 𝓘(ℝ) ∞ r)
    (hgradr : IsSmoothVectorField (gradient g r))
    {X : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    {p : M} (hp : p ∈ U) :
    D.cov p (gradient g r p) (gradient g r) = 0
    ∧ hessianOperatorCovariantDerivative D.toAffineConnection g r
          (gradient g r) X p
        + hessianOperator D.toAffineConnection g r p
            (hessianOperator D.toAffineConnection g r p (X p))
      = -curvatureTensor D.toAffineConnection X (gradient g r)
          (gradient g r) p := by
  have hgeo := covField_gradient_self_eqOn_zero D hU hr hrs hgradr
  refine ⟨hgeo p hp, ?_⟩
  -- the field `S(∂_r) = ∇_{∂_r}∂_r` vanishes on the open set `U`
  have hSgrad : IsSmoothVectorField
      (D.toAffineConnection.covField (gradient g r) (gradient g r)) :=
    D.smooth_cov hgradr hgradr
  have hzero : IsSmoothVectorField (fun q : M => (0 : TangentSpace I q)) := by
    simpa using (0 : SmoothVectorField I M).smooth
  have hvanish : D.cov p (X p)
      (D.toAffineConnection.covField (gradient g r) (gradient g r)) = 0 := by
    have hEqOn : Set.EqOn
        (D.toAffineConnection.covField (gradient g r) (gradient g r))
        (fun q : M => (0 : TangentSpace I q)) U := fun q hq => hgeo q hq
    rw [connection_local_openSet D.toAffineConnection (X p) hSgrad hzero hU hp
      hEqOn]
    exact D.toAffineConnection.cov_zero_field p (X p)
  have hform := (radialCurvatureEquation D hrs hX hX hgradr p).1
  rw [hvanish, sub_zero] at hform
  exact hform

/-- **Math.** **Proposition 3.2.11** (Petersen,
`prop:pet-ch3-distance-function-curvature-equations`): the fundamental
equations for a distance function `r` on `U` — at every `p ∈ U`,

1. `L_{∂_r}g = 2 Hess r`;
2. `(∇_{∂_r}Hess r)(X,Y) + Hess²r(X,Y) = −R(X,∂_r,∂_r,Y)`;
3. `(L_{∂_r}Hess r)(X,Y) − Hess²r(X,Y) = −R(X,∂_r,∂_r,Y)`.

(1) is the definition of the Hessian through the Lie derivative; (2) and (3)
are the second and third radial curvature equations, using
`Hess(½|∇r|²) = Hess(½) = 0` on `U`. -/
theorem distanceFunction_curvatureEquations {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {U : Set M} (hU : IsOpen U) {r : M → ℝ}
    (hr : IsDistanceFunction g U r) (hrs : ContMDiff I 𝓘(ℝ) ∞ r)
    (hgradr : IsSmoothVectorField (gradient g r))
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    {p : M} (hp : p ∈ U) :
    lieDerivativeTensor I (gradient g r) (metricOperator g) ![X, Y] p
        = 2 * hessianLieDerivative g r ![X, Y] p
    ∧ covariantDerivativeTensor D.toAffineConnection (gradient g r)
          (hessianLieDerivative g r) ![X, Y] p
        + hessianOperatorSquared D.toAffineConnection g r p (X p) (Y p)
      = -curvatureTensorFour D X (gradient g r) (gradient g r) Y p
    ∧ lieDerivativeTensor I (gradient g r) (hessianLieDerivative g r) ![X, Y] p
        - hessianOperatorSquared D.toAffineConnection g r p (X p) (Y p)
      = -curvatureTensorFour D X (gradient g r) (gradient g r) Y p := by
  -- `Hess(½|∇r|²)` vanishes at points of `U`
  have hgeo := covField_gradient_self_eqOn_zero D hU hr hrs hgradr
  have hgradsq := gradient_half_normSq D hrs hgradr
  have hgradsq_smooth : IsSmoothVectorField (gradient g
      (fun q => (1 / 2 : ℝ)
        * g.metricInner q (gradient g r q) (gradient g r q))) := by
    rw [hgradsq]
    exact D.smooth_cov hgradr hgradr
  have hsq_smooth : ContMDiff I 𝓘(ℝ) ∞
      (fun q => (1 / 2 : ℝ)
        * g.metricInner q (gradient g r q) (gradient g r q)) := by
    simpa [smul_eq_mul] using
      (contMDiff_const (I := I) (I' := 𝓘(ℝ, ℝ)) (c := (1 / 2 : ℝ))).smul
        (contMDiff_metricInner_gradient_self hgradr)
  have hthird : hessianLieDerivative g
        (fun q => (1 / 2 : ℝ)
          * g.metricInner q (gradient g r q) (gradient g r q)) ![X, Y] p
      = 0 := by
    rw [hessianLieDerivative_eq_metricInner_cov D hsq_smooth hX hY
      hgradsq_smooth p, hgradsq]
    have hSgrad : IsSmoothVectorField
        (D.toAffineConnection.covField (gradient g r) (gradient g r)) :=
      D.smooth_cov hgradr hgradr
    have hzero : IsSmoothVectorField (fun q : M => (0 : TangentSpace I q)) := by
      simpa using (0 : SmoothVectorField I M).smooth
    have hEqOn : Set.EqOn
        (D.toAffineConnection.covField (gradient g r) (gradient g r))
        (fun q : M => (0 : TangentSpace I q)) U := fun q hq => hgeo q hq
    rw [connection_local_openSet D.toAffineConnection (X p) hSgrad hzero hU hp
      hEqOn, D.toAffineConnection.cov_zero_field, g.metricInner_zero_left]
  refine ⟨?_, ?_, ?_⟩
  · rw [hessianLieDerivative_apply]
    ring
  · have h := (radialCurvatureEquation D hrs hX hY hgradr p).2.1
    rw [hthird, sub_zero] at h
    exact h
  · have h := (radialCurvatureEquation D hrs hX hY hgradr p).2.2
    rw [hthird, sub_zero] at h
    exact h

end DistanceFunctionEquations

/-! ## §3.2.4 — the fundamental equations along Jacobi fields -/

section JacobiEquations

variable [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** **The second-order Jacobi equation** (Petersen §3.2.4,
`prop:pet-ch3-jacobi-second-order-equation`): a Jacobi field `J` for the
distance function `r` satisfies `∇_{∂_r}∇_{∂_r}J = −R(J,∂_r)∂_r` on `U` —
differentiate the first-order equation `∇_{∂_r}J = S(J)` and apply
Corollary 3.2.10. -/
theorem jacobiField_secondOrderEquation {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {U : Set M} (hU : IsOpen U) {r : M → ℝ}
    (hr : IsDistanceFunction g U r) (hrs : ContMDiff I 𝓘(ℝ) ∞ r)
    (hgradr : IsSmoothVectorField (gradient g r))
    {J : Π x : M, TangentSpace I x} (hJ : IsSmoothVectorField J)
    (hJac : IsJacobiField g U r J) {p : M} (hp : p ∈ U) :
    D.cov p (gradient g r p)
        (D.toAffineConnection.covField (gradient g r) J)
      = -curvatureTensor D.toAffineConnection J (gradient g r)
          (gradient g r) p := by
  -- on `U`, the first-order Jacobi equation converts `∇_{∂_r}J` into `S(J)`
  have hfirst : ∀ q ∈ U, D.cov q (gradient g r q) J
      = D.cov q (J q) (gradient g r) := fun q hq =>
    (jacobiField_equivalentEquation D hgradr hJ q).mp (hJac q hq)
  have hcovJ : IsSmoothVectorField
      (D.toAffineConnection.covField (gradient g r) J) := D.smooth_cov hgradr hJ
  have hcovS : IsSmoothVectorField
      (D.toAffineConnection.covField J (gradient g r)) := D.smooth_cov hJ hgradr
  -- locality: replace the field `∇_{∂_r}J` by `S(J)` before differentiating
  have hloc : D.cov p (gradient g r p)
        (D.toAffineConnection.covField (gradient g r) J)
      = D.cov p (gradient g r p)
          (D.toAffineConnection.covField J (gradient g r)) :=
    connection_local_openSet D.toAffineConnection (gradient g r p) hcovJ hcovS
      hU hp fun q hq => hfirst q hq
  -- `∇_{∂_r}(S(J)) = ∇²_{∂_r,J}∂_r + S(∇_{∂_r}J) = (∇_{∂_r}S)(J) + S²(J)`
  have hsplit : D.cov p (gradient g r p)
        (D.toAffineConnection.covField J (gradient g r))
      = secondCovariantDerivativeField D.toAffineConnection (gradient g r) J
          (gradient g r) p
        + D.cov p (D.cov p (gradient g r p) J) (gradient g r) := by
    rw [secondCovariantDerivativeField_apply]
    simp only [AffineConnection.covField_apply]
    module
  -- the correction term is `S²(J)` by the first-order Jacobi equation at `p`
  have hcorr : D.cov p (D.cov p (gradient g r p) J) (gradient g r)
      = hessianOperator D.toAffineConnection g r p
          (hessianOperator D.toAffineConnection g r p (J p)) := by
    rw [hfirst p hp]
    rfl
  have hcor := (radialEquation_distanceFunction D hU hr hrs hgradr hJ hp).2
  rw [hloc, hsplit, hcorr,
    ← hessianOperatorCovariantDerivative_eq_secondCovariantDerivative
      D.toAffineConnection g r (gradient g r) J p]
  exact hcor

/-- **Math.** **The fundamental equations along Jacobi fields** (Petersen
§3.2.4, `prop:pet-ch3-jacobi-field-curvature-equations`): for Jacobi fields
`J₁, J₂` of the distance function `r`, at `p ∈ U`,

1. `∂_r g(J₁,J₂) = 2 Hess r(J₁,J₂)`;
2. `∂_r(Hess r(J₁,J₂)) − Hess²r(J₁,J₂) = −R(J₁,∂_r,∂_r,J₂)`.

Lie derivatives along `∂_r` of functions built from Jacobi fields reduce to
plain directional derivatives, since `L_{∂_r}Jᵢ = 0`. -/
theorem jacobiField_curvatureEquations {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {U : Set M} (hU : IsOpen U) {r : M → ℝ}
    (hr : IsDistanceFunction g U r) (hrs : ContMDiff I 𝓘(ℝ) ∞ r)
    (hgradr : IsSmoothVectorField (gradient g r))
    {J₁ J₂ : Π x : M, TangentSpace I x}
    (hJ₁ : IsSmoothVectorField J₁) (hJ₂ : IsSmoothVectorField J₂)
    (hJac₁ : IsJacobiField g U r J₁) (hJac₂ : IsJacobiField g U r J₂)
    {p : M} (hp : p ∈ U) :
    directionalDerivative (gradient g r)
        (fun q => g.metricInner q (J₁ q) (J₂ q)) p
      = 2 * hessianLieDerivative g r ![J₁, J₂] p
    ∧ directionalDerivative (gradient g r)
          (hessianLieDerivative g r ![J₁, J₂]) p
        - hessianOperatorSquared D.toAffineConnection g r p (J₁ p) (J₂ p)
      = -curvatureTensorFour D J₁ (gradient g r) (gradient g r) J₂ p := by
  have hL₁ : IsSmoothVectorField (lieDerivativeVectorField I (gradient g r) J₁) :=
    hgradr.lieDerivativeVectorField hJ₁
  have hL₂ : IsSmoothVectorField (lieDerivativeVectorField I (gradient g r) J₂) :=
    hgradr.lieDerivativeVectorField hJ₂
  constructor
  · -- metric compatibility + the first-order Jacobi equation at `p`
    have hcompat := D.metric_compat hJ₁ hJ₂ p (gradient g r p)
    rw [dirTangent_eq_directionalDerivative] at hcompat
    have h₁ : D.cov p (gradient g r p) J₁ = D.cov p (J₁ p) (gradient g r) :=
      (jacobiField_equivalentEquation D hgradr hJ₁ p).mp (hJac₁ p hp)
    have h₂ : D.cov p (gradient g r p) J₂ = D.cov p (J₂ p) (gradient g r) :=
      (jacobiField_equivalentEquation D hgradr hJ₂ p).mp (hJac₂ p hp)
    rw [h₁, h₂] at hcompat
    -- both summands are `Hess r(J₁,J₂)`
    have hb₁ : g.metricInner p (D.cov p (J₁ p) (gradient g r)) (J₂ p)
        = hessianLieDerivative g r ![J₁, J₂] p :=
      (hessianLieDerivative_eq_metricInner_cov D hrs hJ₁ hJ₂ hgradr p).symm
    have hb₂ : g.metricInner p (J₁ p) (D.cov p (J₂ p) (gradient g r))
        = hessianLieDerivative g r ![J₁, J₂] p := by
      rw [g.metricInner_comm,
        ← hessianLieDerivative_eq_metricInner_cov D hrs hJ₂ hJ₁ hgradr p]
      exact (hessianLieDerivative_symm D hrs hJ₂ hJ₁ hgradr p)
    rw [hb₁, hb₂] at hcompat
    linarith [hcompat]
  · -- start from equation (3) of Proposition 3.2.11
    have h₃ := (distanceFunction_curvatureEquations D hU hr hrs hgradr hJ₁ hJ₂
      hp).2.2
    -- the Lie derivative of `Hess r(J₁,J₂)` reduces to `∂_r(Hess r(J₁,J₂))`
    have hlie : lieDerivativeTensor I (gradient g r)
          (hessianLieDerivative g r) ![J₁, J₂] p
        = directionalDerivative (gradient g r)
            (hessianLieDerivative g r ![J₁, J₂]) p := by
      rw [lieDerivativeTensor_formula, Fin.sum_univ_two, update_pair_fst,
        update_pair_snd]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have hc₁ : hessianLieDerivative g r
            ![lieDerivativeVectorField I (gradient g r) J₁, J₂] p = 0 := by
        rw [hessianLieDerivative_eq_metricInner_cov D hrs hL₁ hJ₂ hgradr p,
          hJac₁ p hp, D.toAffineConnection.cov_zero_direction,
          g.metricInner_zero_left]
      have hc₂ : hessianLieDerivative g r
            ![J₁, lieDerivativeVectorField I (gradient g r) J₂] p = 0 := by
        rw [hessianLieDerivative_eq_metricInner_cov D hrs hJ₁ hL₂ hgradr p,
          hJac₂ p hp, g.metricInner_zero_right]
      rw [hc₁, hc₂]
      ring
    rw [hlie] at h₃
    exact h₃

omit [LocallyCompactSpace M] in
/-- **Math.** **Jacobi fields on a product neighborhood** (Petersen §3.2.4,
`rem:pet-ch3-jacobi-field-product-neighborhood`): the geometric content of the
reduction `g = dr² + g_r` on `(a,b) × H` — the Hessian of `r` has no radial
component, `Hess r(∂_r, J) = 0`, and a Jacobi field initially tangent to a
level set of `r` stays tangent, `∂_r g(∂_r, J) = 0`; hence the fundamental
equations of `prop:pet-ch3-jacobi-field-curvature-equations` restrict to the
level sets, where they read `∂_r g_r = 2 Hess r` and
`∂_r Hess r − Hess²r = −R(·,∂_r,∂_r,·)`. -/
theorem jacobiField_productNeighborhood {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {U : Set M} (hU : IsOpen U) {r : M → ℝ}
    (hr : IsDistanceFunction g U r) (hrs : ContMDiff I 𝓘(ℝ) ∞ r)
    (hgradr : IsSmoothVectorField (gradient g r))
    {J : Π x : M, TangentSpace I x} (hJ : IsSmoothVectorField J)
    (hJac : IsJacobiField g U r J) {p : M} (hp : p ∈ U) :
    hessianLieDerivative g r ![gradient g r, J] p = 0
    ∧ directionalDerivative (gradient g r)
        (fun q => g.metricInner q (gradient g r q) (J q)) p = 0 := by
  have hgeo := covField_gradient_self_eqOn_zero D hU hr hrs hgradr
  have hhess : hessianLieDerivative g r ![gradient g r, J] p = 0 := by
    rw [hessianLieDerivative_eq_metricInner_cov D hrs hgradr hJ hgradr p,
      hgeo p hp, g.metricInner_zero_left]
  refine ⟨hhess, ?_⟩
  -- `∂_r g(∂_r, J) = g(∇_{∂_r}∂_r, J) + g(∂_r, ∇_{∂_r}J) = 0 + Hess r(J, ∂_r)`
  have hcompat := D.metric_compat hgradr hJ p (gradient g r p)
  rw [dirTangent_eq_directionalDerivative] at hcompat
  have hfirst : D.cov p (gradient g r p) J = D.cov p (J p) (gradient g r) :=
    (jacobiField_equivalentEquation D hgradr hJ p).mp (hJac p hp)
  rw [hgeo p hp, g.metricInner_zero_left, hfirst] at hcompat
  have hb : g.metricInner p (gradient g r p) (D.cov p (J p) (gradient g r))
      = hessianLieDerivative g r ![gradient g r, J] p := by
    rw [g.metricInner_comm,
      ← hessianLieDerivative_eq_metricInner_cov D hrs hJ hgradr hgradr p]
    exact hessianLieDerivative_symm D hrs hJ hgradr hgradr p
  rw [hb, hhess] at hcompat
  linarith [hcompat]

end JacobiEquations

/-! ## §3.2.4–§3.2.6 — sectional curvature along `∂_r`, parallel fields, and
the Riccati sign analysis -/

section SectionalRadial

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** **The radial curvature term via sectional curvature** (Petersen
§3.2.4, `lem:pet-ch3-jacobi-field-sectional-curvature-formula`): for `X`
orthogonal to `∂_r` at `p ∈ U`,
`R(X,∂_r,∂_r,X) = sec(∂_r, X) · g(X,X)` (both sides vanish when `X_p = 0`);
hence for a Jacobi field `J` the fundamental equation reads
`∂_r(Hess r(J,J)) − Hess²r(J,J) = −sec(∂_r,J) g(J,J)`, which still couples the
Hessian equation to the metric through `g(J,J)`. -/
theorem jacobiField_sectionalCurvatureFormula {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {U : Set M} (hU : IsOpen U) {r : M → ℝ}
    (hr : IsDistanceFunction g U r) (hrs : ContMDiff I 𝓘(ℝ) ∞ r)
    (hgradr : IsSmoothVectorField (gradient g r))
    {X : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    {p : M} (hp : p ∈ U)
    (horth : g.metricInner p (X p) (gradient g r p) = 0) :
    curvatureTensorFour D X (gradient g r) (gradient g r) X p
      = sectionalCurvature D p (gradient g r p) (X p)
        * g.metricInner p (X p) (X p)
    ∧ (IsJacobiField g U r X →
        directionalDerivative (gradient g r)
            (hessianLieDerivative g r ![X, X]) p
          - hessianOperatorSquared D.toAffineConnection g r p (X p) (X p)
        = -(sectionalCurvature D p (gradient g r p) (X p)
            * g.metricInner p (X p) (X p))) := by
  have hform : curvatureTensorFour D X (gradient g r) (gradient g r) X p
      = sectionalCurvature D p (gradient g r p) (X p)
        * g.metricInner p (X p) (X p) := by
    by_cases hX0 : X p = 0
    · -- both sides vanish
      have hL : curvatureTensorFour D X (gradient g r) (gradient g r) X p
          = g.metricInner p
              (curvatureTensor D.toAffineConnection X (gradient g r)
                (gradient g r) p) (X p) := rfl
      rw [hL, hX0, g.metricInner_zero_right, g.metricInner_zero_right, mul_zero]
    · -- the bivector norm collapses to `g(X,X)` by the eikonal equation
      have hbiv : bivectorInnerProduct g p (gradient g r p) (X p)
            (gradient g r p) (X p) = g.metricInner p (X p) (X p) := by
        have hcomm : g.metricInner p (gradient g r p) (X p)
            = g.metricInner p (X p) (gradient g r p) := g.metricInner_comm ..
        simp only [bivectorInnerProduct]
        rw [hr.2 p hp, hcomm, horth]
        ring
      have hne : g.metricInner p (X p) (X p) ≠ 0 :=
        (g.metricInner_self_pos p (X p) hX0).ne'
      rw [sectionalCurvature_eq_curvatureTensorFourAt, hbiv,
        curvatureTensorFourAt_apply D hX hgradr hgradr p,
        div_mul_cancel₀ _ hne]
  refine ⟨hform, fun hJac => ?_⟩
  have h₂ := (jacobiField_curvatureEquations D hU hr hrs hgradr hX hX hJac hJac
    hp).2
  rw [h₂, hform]

/-- **Math.** **The curvature equation on parallel fields** (Petersen §3.2.5,
`prop:pet-ch3-parallel-field-curvature-equation`): for parallel fields `X, Y`
of the distance function `r`, at `p ∈ U`,

1. `∂_r g(X,Y) = 0` (inner products of parallel fields are constant in `r`);
2. `∂_r(Hess r(X,Y)) + Hess²r(X,Y) = −R(X,∂_r,∂_r,Y)`;
3. for a **unit** parallel field `X` orthogonal to `∂_r`,
   `∂_r(Hess r(X,X)) + Hess²r(X,X) = −sec(∂_r, X)` — decoupled from the
   metric, since `g(X,X) ≡ 1`.

In contrast to Jacobi fields, the covariant-derivative form (2) is the one
whose corrections vanish (`∇_{∂_r}X = 0`), producing the sign `+Hess²r`. -/
theorem parallelField_curvatureEquation {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {U : Set M} (hU : IsOpen U) {r : M → ℝ}
    (hr : IsDistanceFunction g U r) (hrs : ContMDiff I 𝓘(ℝ) ∞ r)
    (hgradr : IsSmoothVectorField (gradient g r))
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hPX : IsParallelField D.toAffineConnection g U r X)
    (hPY : IsParallelField D.toAffineConnection g U r Y)
    {p : M} (hp : p ∈ U) :
    directionalDerivative (gradient g r)
        (fun q => g.metricInner q (X q) (Y q)) p = 0
    ∧ directionalDerivative (gradient g r)
          (hessianLieDerivative g r ![X, Y]) p
        + hessianOperatorSquared D.toAffineConnection g r p (X p) (Y p)
      = -curvatureTensorFour D X (gradient g r) (gradient g r) Y p
    ∧ (g.metricInner p (X p) (gradient g r p) = 0 →
        g.metricInner p (X p) (X p) = 1 →
        directionalDerivative (gradient g r)
            (hessianLieDerivative g r ![X, X]) p
          + hessianOperatorSquared D.toAffineConnection g r p (X p) (X p)
        = -sectionalCurvature D p (gradient g r p) (X p)) := by
  have hNX : IsSmoothVectorField
      (D.toAffineConnection.covField (gradient g r) X) := D.smooth_cov hgradr hX
  have hNY : IsSmoothVectorField
      (D.toAffineConnection.covField (gradient g r) Y) := D.smooth_cov hgradr hY
  -- (1): metric compatibility, both covariant derivatives vanish at `p`
  have hfirst : directionalDerivative (gradient g r)
      (fun q => g.metricInner q (X q) (Y q)) p = 0 := by
    have hcompat := D.metric_compat hX hY p (gradient g r p)
    rw [dirTangent_eq_directionalDerivative] at hcompat
    rw [hcompat, hPX p hp, hPY p hp, g.metricInner_zero_left,
      g.metricInner_zero_right]
    ring
  -- (2): the covariant-derivative form of the fundamental equation, with
  -- vanishing corrections
  have hsecond : directionalDerivative (gradient g r)
        (hessianLieDerivative g r ![X, Y]) p
      + hessianOperatorSquared D.toAffineConnection g r p (X p) (Y p)
      = -curvatureTensorFour D X (gradient g r) (gradient g r) Y p := by
    have h₂ := (distanceFunction_curvatureEquations D hU hr hrs hgradr hX hY
      hp).2.1
    have hexp : covariantDerivativeTensor D.toAffineConnection (gradient g r)
          (hessianLieDerivative g r) ![X, Y] p
        = directionalDerivative (gradient g r)
            (hessianLieDerivative g r ![X, Y]) p := by
      rw [covariantDerivativeTensor_formula, Fin.sum_univ_two, update_pair_fst,
        update_pair_snd]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have hc₁ : hessianLieDerivative g r
            ![D.toAffineConnection.covField (gradient g r) X, Y] p = 0 := by
        rw [hessianLieDerivative_eq_metricInner_cov D hrs hNX hY hgradr p]
        have hzero : D.toAffineConnection.covField (gradient g r) X p = 0 :=
          hPX p hp
        rw [hzero, D.toAffineConnection.cov_zero_direction,
          g.metricInner_zero_left]
      have hc₂ : hessianLieDerivative g r
            ![X, D.toAffineConnection.covField (gradient g r) Y] p = 0 := by
        rw [hessianLieDerivative_eq_metricInner_cov D hrs hX hNY hgradr p]
        have hzero : D.toAffineConnection.covField (gradient g r) Y p = 0 :=
          hPY p hp
        rw [hzero, g.metricInner_zero_right]
      rw [hc₁, hc₂]
      ring
    rw [hexp] at h₂
    exact h₂
  refine ⟨hfirst, hsecond, fun horth hunit => ?_⟩
  -- (3): specialize (2) to `Y = X` and rewrite the curvature term through the
  -- sectional curvature of the radial plane
  have hXX : directionalDerivative (gradient g r)
        (hessianLieDerivative g r ![X, X]) p
      + hessianOperatorSquared D.toAffineConnection g r p (X p) (X p)
      = -curvatureTensorFour D X (gradient g r) (gradient g r) X p := by
    have h := (distanceFunction_curvatureEquations D hU hr hrs hgradr hX hX
      hp).2.1
    have hexp : covariantDerivativeTensor D.toAffineConnection (gradient g r)
          (hessianLieDerivative g r) ![X, X] p
        = directionalDerivative (gradient g r)
            (hessianLieDerivative g r ![X, X]) p := by
      rw [covariantDerivativeTensor_formula, Fin.sum_univ_two, update_pair_fst,
        update_pair_snd]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have hc₁ : hessianLieDerivative g r
            ![D.toAffineConnection.covField (gradient g r) X, X] p = 0 := by
        rw [hessianLieDerivative_eq_metricInner_cov D hrs hNX hX hgradr p]
        have hzero : D.toAffineConnection.covField (gradient g r) X p = 0 :=
          hPX p hp
        rw [hzero, D.toAffineConnection.cov_zero_direction,
          g.metricInner_zero_left]
      have hc₂ : hessianLieDerivative g r
            ![X, D.toAffineConnection.covField (gradient g r) X] p = 0 := by
        rw [hessianLieDerivative_eq_metricInner_cov D hrs hX hNX hgradr p]
        have hzero : D.toAffineConnection.covField (gradient g r) X p = 0 :=
          hPX p hp
        rw [hzero, g.metricInner_zero_right]
      rw [hc₁, hc₂]
      ring
    rw [hexp] at h
    exact h
  have hsec := (jacobiField_sectionalCurvatureFormula D hU hr hrs hgradr hX hp
    horth).1
  rw [hsec, hunit, mul_one] at hXX
  exact hXX

/-- **Math.** **External force versus internal reaction** (Petersen §3.2.6,
`rem:pet-ch3-external-force-internal-reaction`): in the rewritten fundamental
equations
`(∇_{∂_r}Hess r)(X,X) = −R(X,∂_r,∂_r,X) − Hess²r(X,X)` and
`(L_{∂_r}Hess r)(X,X) = −R(X,∂_r,∂_r,X) + Hess²r(X,X)`,
the curvature term is a fixed *external force* while the sign-definite
`Hess²r` is an *internal reaction*: for `X` orthogonal to `∂_r`,

* if `sec(∂_r, X) ≤ 0` then `(L_{∂_r}Hess r)(X,X) ≥ 0`
  (positive `Hess r` stays positive);
* if `sec(∂_r, X) ≥ 0` then `(∇_{∂_r}Hess r)(X,X) ≤ 0`
  (nonpositive `Hess r` stays nonpositive). -/
theorem externalForceInternalReaction {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {U : Set M} (hU : IsOpen U) {r : M → ℝ}
    (hr : IsDistanceFunction g U r) (hrs : ContMDiff I 𝓘(ℝ) ∞ r)
    (hgradr : IsSmoothVectorField (gradient g r))
    {X : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    {p : M} (hp : p ∈ U)
    (horth : g.metricInner p (X p) (gradient g r p) = 0) :
    (sectionalCurvature D p (gradient g r p) (X p) ≤ 0 →
      0 ≤ lieDerivativeTensor I (gradient g r) (hessianLieDerivative g r)
        ![X, X] p)
    ∧ (0 ≤ sectionalCurvature D p (gradient g r p) (X p) →
      covariantDerivativeTensor D.toAffineConnection (gradient g r)
        (hessianLieDerivative g r) ![X, X] p ≤ 0) := by
  -- the curvature term through the sectional curvature, and the two
  -- sign-definite quantities
  have hsec := (jacobiField_sectionalCurvatureFormula D hU hr hrs hgradr hX hp
    horth).1
  have hXXnn : (0 : ℝ) ≤ g.metricInner p (X p) (X p) :=
    g.metricInner_self_nonneg p (X p)
  have hsqnn : (0 : ℝ)
      ≤ hessianOperatorSquared D.toAffineConnection g r p (X p) (X p) := by
    rw [hessianOperatorSquared_eq_metricInner D hrs hX hX hgradr p]
    exact g.metricInner_self_nonneg p _
  have heqs := distanceFunction_curvatureEquations D hU hr hrs hgradr hX hX hp
  constructor
  · intro hneg
    have h₃ := heqs.2.2
    have hforce : (0 : ℝ)
        ≤ -curvatureTensorFour D X (gradient g r) (gradient g r) X p := by
      rw [hsec]
      have := mul_nonneg (neg_nonneg.mpr hneg) hXXnn
      linarith [this]
    linarith [h₃, hsqnn, hforce]
  · intro hpos
    have h₂ := heqs.2.1
    have hforce : -curvatureTensorFour D X (gradient g r) (gradient g r) X p
        ≤ 0 := by
      rw [hsec]
      have := mul_nonneg hpos hXXnn
      linarith [this]
    linarith [h₂, hsqnn, hforce]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M] in
/-- **Eng.** A pointwise `2`-dimensional linear-algebra fact for the Riemannian
metric `g`. If the tangent fibre has dimension `2` and both `x` and `y` are
`g`-orthogonal to a nonzero vector `n`, then `x` and `y` lie in the (necessarily
`1`-dimensional) `g`-orthogonal complement of `n`, so they are colinear and their
Gram determinant vanishes: `g(x,x)·g(y,y) = g(x,y)²`.

This is the linear-algebra core of the two-dimensional sectional-curvature
formula: applied with `n = ∂_r`, `x = S(J)` and `y = J` it reduces
`Hess²r(J,J) = g(S(J),S(J))` to `Hess r(J,J)²/g(J,J)`. -/
theorem metricInner_gram_det_eq_of_orthogonal_dim_two
    {g : RiemannianMetric I M} (p : M) (n x y : TangentSpace I p)
    (hdim : Module.finrank ℝ E = 2) (hn : n ≠ 0)
    (hxn : g.metricInner p x n = 0) (hyn : g.metricInner p y n = 0) :
    g.metricInner p x x * g.metricInner p y y
      = g.metricInner p x y * g.metricInner p x y := by
  classical
  -- the `g`-inner-product-with-`n` functional on the tangent fibre
  set φ : TangentSpace I p →ₗ[ℝ] ℝ :=
    { toFun := fun v => g.metricInner p v n
      map_add' := fun a b => g.metricInner_add_left p a b n
      map_smul' := fun c a => by
        simp only [g.metricInner_smul_left, RingHom.id_apply, smul_eq_mul] } with hφdef
  have hφx : φ x = 0 := hxn
  have hφy : φ y = 0 := hyn
  have hφne : φ ≠ 0 := by
    intro h
    have : g.metricInner p n n = 0 := by
      have : φ n = 0 := by rw [h]; rfl
      exact this
    exact (ne_of_gt (g.metricInner_self_pos p n hn)) this
  -- rank–nullity forces `finrank (ker φ) = 1`
  have hdimT : Module.finrank ℝ (TangentSpace I p) = 2 := hdim
  have hrank : Module.finrank ℝ (LinearMap.ker φ) = 1 := by
    have h := φ.finrank_range_add_finrank_ker
    have hr : Module.finrank ℝ (LinearMap.range φ) = 1 := by
      have htop : LinearMap.range φ = ⊤ :=
        LinearMap.range_eq_top.mpr (LinearMap.surjective_of_ne_zero hφne)
      rw [htop, finrank_top]; simp
    rw [hr, hdimT] at h; omega
  -- two vectors in a `1`-dimensional space are linearly dependent
  have hdep : ¬ LinearIndependent ℝ
      ![(⟨x, hφx⟩ : LinearMap.ker φ), ⟨y, hφy⟩] := by
    intro hli
    have hle := hli.fintype_card_le_finrank
    rw [hrank] at hle
    simp at hle
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨c, hsum, i, hci⟩ := hdep
  -- extract the nontrivial relation `a•x + b•y = 0` in the tangent fibre
  have hrel : c 0 • x + c 1 • y = 0 := by
    have hker : c 0 • (⟨x, hφx⟩ : LinearMap.ker φ) + c 1 • ⟨y, hφy⟩ = 0 := by
      rw [← hsum]; simp [Fin.sum_univ_two]
    have h2 := congrArg (Submodule.subtype (LinearMap.ker φ)) hker
    simpa using h2
  have hab : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
    fin_cases i
    · exact Or.inl hci
    · exact Or.inr hci
  -- pair the relation against `x` and `y`
  set Gxx := g.metricInner p x x with hGxx
  set Gxy := g.metricInner p x y with hGxy
  set Gyy := g.metricInner p y y with hGyy
  have hi : c 0 * Gxx + c 1 * Gxy = 0 := by
    have := congrArg (fun v => g.metricInner p v x) hrel
    simp only [g.metricInner_add_left, g.metricInner_smul_left,
      g.metricInner_zero_left] at this
    rw [g.metricInner_comm p y x] at this
    linarith [this]
  have hii : c 0 * Gxy + c 1 * Gyy = 0 := by
    have := congrArg (fun v => g.metricInner p v y) hrel
    simp only [g.metricInner_add_left, g.metricInner_smul_left,
      g.metricInner_zero_left] at this
    linarith [this]
  -- the homogeneous `2×2` system with a nontrivial solution has zero determinant
  have haD : c 0 * (Gxx * Gyy - Gxy * Gxy) = 0 := by
    linear_combination Gyy * hi - Gxy * hii
  have hbD : c 1 * (Gxx * Gyy - Gxy * Gxy) = 0 := by
    linear_combination Gxx * hii - Gxy * hi
  have hD : Gxx * Gyy - Gxy * Gxy = 0 := by
    rcases hab with ha | hb
    · exact (mul_eq_zero.mp haD).resolve_left ha
    · exact (mul_eq_zero.mp hbD).resolve_left hb
  linarith [hD]

/-- **Math.** **Two-dimensional sectional curvature via a distance function**
(Petersen §3.2.4, Example 3.2.12, `ex:pet-ch3-two-dim-sectional-curvature-formula`).
On a surface (`dim M = 2`) with a distance function `r`, the metric can be written
`g = dr² + ρ²dθ²`, so a coordinate Jacobi field `J` in the role of `∂_θ`,
orthogonal to `∂_r`, has length `g(J,J) = ρ²`. Then the sectional curvature of the
tangent plane is `sec = -∂_r²ρ/ρ`.

Here the `ρ`-parametrization is stated invariantly: `J` is any Jacobi field of `r`,
orthogonal to `∂_r` at `p`, whose squared length equals a smooth square `ρ²` on
`U`. In dimension `2` the `g`-orthogonal complement of `∂_r` is a line, so the
shape operator `S` maps `J` to a multiple of itself; this collapses
`Hess²r(J,J) = g(S(J),S(J))` to `(∂_rρ)²`
(`metricInner_gram_det_eq_of_orthogonal_dim_two`). Combined with the Jacobi
fundamental equations (`jacobiField_curvatureEquations`,
`jacobiField_sectionalCurvatureFormula`) and `∂_r g(J,J) = 2 Hess r(J,J)` written
through `ρ`, this yields the formula. -/
theorem twoDimensional_sectionalCurvature_formula {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {U : Set M} (hU : IsOpen U) {r : M → ℝ}
    (hr : IsDistanceFunction g U r) (hrs : ContMDiff I 𝓘(ℝ) ∞ r)
    (hgradr : IsSmoothVectorField (gradient g r))
    (hdim : Module.finrank ℝ E = 2)
    {J : Π x : M, TangentSpace I x} (hJ : IsSmoothVectorField J)
    (hJac : IsJacobiField g U r J)
    {ρ : M → ℝ} (hρs : ContMDiff I 𝓘(ℝ) ∞ ρ)
    (hρ : ∀ q ∈ U, g.metricInner q (J q) (J q) = ρ q ^ 2)
    {p : M} (hp : p ∈ U)
    (horth : g.metricInner p (J p) (gradient g r p) = 0) (hρp : ρ p ≠ 0) :
    sectionalCurvature D p (gradient g r p) (J p)
      = (-directionalDerivative (gradient g r)
            (directionalDerivative (gradient g r) ρ) p) / ρ p := by
  classical
  have hdρ : ContMDiff I 𝓘(ℝ) ∞ (directionalDerivative (gradient g r) ρ) :=
    hgradr.directionalDerivative_contMDiff hρs
  -- `∂_r` is nonzero, since `g(∂_r,∂_r) = 1`
  have hnp : gradient g r p ≠ 0 := by
    intro h
    have h1 := hr.2 p hp
    rw [h, g.metricInner_zero_left] at h1
    exact one_ne_zero h1.symm
  -- (F3) locally on `U`, `Hess r(J,J) = ρ · ∂_r ρ`
  have hH_local : ∀ q ∈ U, hessianLieDerivative g r ![J, J] q
      = ρ q * directionalDerivative (gradient g r) ρ q := by
    intro q hq
    have hjac := (jacobiField_curvatureEquations D hU hr hrs hgradr hJ hJ hJac hJac hq).1
    have hGJloc : (fun q' => g.metricInner q' (J q') (J q')) =ᶠ[𝓝 q]
        (fun q' => ρ q' ^ 2) := by
      filter_upwards [hU.mem_nhds hq] with q' hq' using hρ q' hq'
    have hcong : directionalDerivative (gradient g r)
          (fun q' => g.metricInner q' (J q') (J q')) q
        = directionalDerivative (gradient g r) (fun q' => ρ q' ^ 2) q := by
      rw [directionalDerivative_apply, directionalDerivative_apply, hGJloc.mfderiv_eq]
      rfl
    rw [hcong] at hjac
    have hpow : (fun q' => ρ q' ^ 2) = ρ * ρ := by funext q'; rw [pow_two]; rfl
    have hmul : directionalDerivative (gradient g r) (fun q' => ρ q' ^ 2) q
        = 2 * (ρ q * directionalDerivative (gradient g r) ρ q) := by
      rw [hpow, directionalDerivative_mul ((hρs q).mdifferentiableAt (by simp))
        ((hρs q).mdifferentiableAt (by simp)) (gradient g r)]
      ring
    rw [hmul] at hjac
    linarith [hjac]
  -- `S(J) = ∇_J∇r` is `g`-orthogonal to `∂_r` (self-adjointness + `S(∂_r) = 0`)
  have hSJ_orth : g.metricInner p (D.cov p (J p) (gradient g r)) (gradient g r p) = 0 := by
    rw [← hessianLieDerivative_eq_metricInner_cov D hrs hJ hgradr hgradr p,
      hessianLieDerivative_symm D hrs hJ hgradr hgradr p,
      hessianLieDerivative_eq_metricInner_cov D hrs hgradr hJ hgradr p,
      covField_gradient_self_eqOn_zero D hU hr hrs hgradr p hp, g.metricInner_zero_left]
  -- (F2) `Hess²r(J,J) = (∂_r ρ)²`, via the `2`-dimensional Gram-determinant fact
  have hHHval : hessianOperatorSquared D.toAffineConnection g r p (J p) (J p)
      = (directionalDerivative (gradient g r) ρ p) ^ 2 := by
    have hcrux := metricInner_gram_det_eq_of_orthogonal_dim_two p (gradient g r p)
      (D.cov p (J p) (gradient g r)) (J p) hdim hnp hSJ_orth horth
    have hHp : g.metricInner p (D.cov p (J p) (gradient g r)) (J p)
        = ρ p * directionalDerivative (gradient g r) ρ p := by
      rw [← hessianLieDerivative_eq_metricInner_cov D hrs hJ hJ hgradr p]
      exact hH_local p hp
    rw [hρ p hp, hHp] at hcrux
    rw [hessianOperatorSquared_eq_metricInner D hrs hJ hJ hgradr p]
    have hρ2 : ρ p ^ 2 ≠ 0 := pow_ne_zero 2 hρp
    have hkey : g.metricInner p (D.cov p (J p) (gradient g r))
          (D.cov p (J p) (gradient g r)) * ρ p ^ 2
        = (directionalDerivative (gradient g r) ρ p) ^ 2 * ρ p ^ 2 := by
      rw [hcrux]; ring
    exact mul_right_cancel₀ hρ2 hkey
  -- (F4) `∂_r(Hess r(J,J)) = ρ · ∂_r²ρ + (∂_r ρ)²`, by the product rule
  have hDH : directionalDerivative (gradient g r) (hessianLieDerivative g r ![J, J]) p
      = ρ p * directionalDerivative (gradient g r)
            (directionalDerivative (gradient g r) ρ) p
        + (directionalDerivative (gradient g r) ρ p) ^ 2 := by
    have hHloc : hessianLieDerivative g r ![J, J] =ᶠ[𝓝 p]
        (fun q => ρ q * directionalDerivative (gradient g r) ρ q) := by
      filter_upwards [hU.mem_nhds hp] with q hq using hH_local q hq
    have hcong : directionalDerivative (gradient g r) (hessianLieDerivative g r ![J, J]) p
        = directionalDerivative (gradient g r)
            (fun q => ρ q * directionalDerivative (gradient g r) ρ q) p := by
      rw [directionalDerivative_apply, directionalDerivative_apply, hHloc.mfderiv_eq]
      rfl
    rw [hcong,
      show (fun q => ρ q * directionalDerivative (gradient g r) ρ q)
          = ρ * directionalDerivative (gradient g r) ρ from rfl,
      directionalDerivative_mul ((hρs p).mdifferentiableAt (by simp))
        ((hdρ p).mdifferentiableAt (by simp)) (gradient g r)]
    ring
  -- (F1) the Jacobi fundamental equation through the sectional curvature
  have hF1 := (jacobiField_sectionalCurvatureFormula D hU hr hrs hgradr hJ hp horth).2 hJac
  rw [hDH, hHHval, hρ p hp] at hF1
  -- `ρ · ∂_r²ρ = -(sec · ρ²)`, so `sec = -∂_r²ρ / ρ`
  have hsimp : ρ p * directionalDerivative (gradient g r)
        (directionalDerivative (gradient g r) ρ) p
      = -(sectionalCurvature D p (gradient g r p) (J p) * ρ p ^ 2) := by
    linarith [hF1]
  have hcancel : directionalDerivative (gradient g r)
        (directionalDerivative (gradient g r) ρ) p
      + sectionalCurvature D p (gradient g r p) (J p) * ρ p = 0 := by
    have hmul : ρ p * (directionalDerivative (gradient g r)
          (directionalDerivative (gradient g r) ρ) p
        + sectionalCurvature D p (gradient g r p) (J p) * ρ p) = 0 := by
      linear_combination hsimp
    exact (mul_eq_zero.mp hmul).resolve_left hρp
  rw [eq_div_iff hρp]
  linarith [hcancel]

end SectionalRadial

end PetersenLib
