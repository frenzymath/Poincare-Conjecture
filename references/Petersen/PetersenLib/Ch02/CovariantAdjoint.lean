import PetersenLib.Ch02.VolumeDivergence
import PetersenLib.Ch02.MetricOperator

/-!
# Petersen Ch. 2, §2.2.4 — The adjoint of the covariant derivative

The **adjoint** `∇*S` of a `(0, t)`-tensor `S` (`t > 0`) relative to an
orthonormal frame `E₁, …, Eₙ` is the `(0, t-1)`-tensor
`(∇*S)(X₂, …, X_t) = -Σᵢ (∇_{Eᵢ}S)(Eᵢ, X₂, …, X_t)`
(`covariantDerivativeAdjoint`, `def:pet-ch2-covariant-derivative-adjoint`), and
**Prop. 2.2.7** identifies the divergence of a vector field with (minus) the
adjoint of its dual `1`-form: `div X = -∇*θ_X`
(`divergence_eq_neg_adjoint_dualForm`, `prop:pet-ch2-divergence-adjoint-formula`).

The proof is the pointwise chain of the blueprint: against a positively oriented
orthonormal frame `Eᵢ` near `x`,
* `(∇_{Eᵢ}θ_X)(Eᵢ) = g(∇_{Eᵢ}X, Eᵢ)` — expand the covariant derivative of a
  `(0,1)`-tensor and cancel the `g(X, ∇_{Eᵢ}Eᵢ)` term against metric
  compatibility (`covariantDerivativeTensor_dualOneForm_diag`);
* `g(∇_{Eᵢ}X, Eᵢ) = ½ (L_X g)(Eᵢ, Eᵢ)` — Petersen's pairing of the connection
  with the metric, via metric compatibility and torsion-freeness
  (`RiemannianConnection.metricInner_cov_self_eq_half_lie`);
* summing and applying the trace formula for the divergence
  (`divergence_trace_formula`) closes the identity.

All tensors here are `(0, k)`-tensors (`TensorOperator I M k`), the faithful
realization of Petersen's `(0, t)`-tensors in this framework; Prop. 2.2.7 only
uses the `(0, 1)` case.  Prop. 2.2.8 (the `L²`-adjoint identity) additionally
needs Stokes' theorem and is deferred.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.2.4.
-/

open Bundle Set Function Finset Module
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Pairing the connection with the metric -/

/-- **Math.** Petersen's pairing identity: for the Levi-Civita connection,
`g(∇_Y X, Y) = ½ (L_X g)(Y, Y)`.  This is the diagonal case of the
metric-compatibility/torsion-freeness computation underlying the Hessian
(Prop. 2.2.6) and the divergence trace formula. -/
theorem RiemannianConnection.metricInner_cov_self_eq_half_lie
    {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y) (p : M) :
    g.metricInner p (D.cov p (Y p) X) (Y p)
      = (1 / 2 : ℝ) * lieDerivativeTensor I X (metricOperator g) ![Y, Y] p := by
  -- expand the Lie derivative of the metric on the diagonal
  have hLg : lieDerivativeTensor I X (metricOperator g) ![Y, Y] p
      = directionalDerivative X (fun q => g.metricInner q (Y q) (Y q)) p
        - g.metricInner p (lieDerivativeVectorField I X Y p) (Y p)
        - g.metricInner p (Y p) (lieDerivativeVectorField I X Y p) := by
    rw [lieDerivativeTensor_formula, Fin.sum_univ_two]
    have h0 : (Function.update (![Y, Y]) (0 : Fin 2) (lieDerivativeVectorField I X Y))
        = ![lieDerivativeVectorField I X Y, Y] := by
      funext j; fin_cases j <;> simp
    have h1 : (Function.update (![Y, Y]) (1 : Fin 2) (lieDerivativeVectorField I X Y))
        = ![Y, lieDerivativeVectorField I X Y] := by
      funext j; fin_cases j <;> simp
    have hYY : (fun q => metricOperator g ![Y, Y] q)
        = fun q => g.metricInner q (Y q) (Y q) := by
      funext q; simp [metricOperator]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h0, h1,
      metricOperator_apply, hYY]
    ring
  -- metric compatibility along X
  have hcompat := D.metric_compat hY hY p (X p)
  rw [dirTangent_eq_directionalDerivative] at hcompat
  -- torsion-freeness: [X, Y] = ∇_X Y - ∇_Y X
  have htf := D.torsion_free hX hY p
  rw [hLg, hcompat, ← htf, g.metricInner_sub_left, g.metricInner_sub_right,
    g.metricInner_comm p (Y p) (D.cov p (X p) Y),
    g.metricInner_comm p (Y p) (D.cov p (Y p) X)]
  ring

/-- **Math.** The **polarized covariant Killing equation**: for the Levi-Civita
connection, `g(∇_U X, V) + g(∇_V X, U) = (L_X g)(U, V)`.  This is the
off-diagonal generalization of `metricInner_cov_self_eq_half_lie` — the
symmetrization of the `(1,1)`-tensor `S : V ↦ ∇_V X` equals the metric Lie
derivative `L_X g`.  It holds for every smooth field `X` (only metric
compatibility and torsion-freeness are used); for a Killing field it collapses to
the skew-symmetry of `S` (`IsKillingField.metricInner_cov_skew`).  Reusable
infrastructure for Killing-field theory (Petersen Ch. 8). -/
theorem RiemannianConnection.metricInner_cov_add_swap_eq_lie
    {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {X U V : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hU : IsSmoothVectorField U)
    (hV : IsSmoothVectorField V) (p : M) :
    g.metricInner p (D.cov p (U p) X) (V p)
        + g.metricInner p (D.cov p (V p) X) (U p)
      = lieDerivativeTensor I X (metricOperator g) ![U, V] p := by
  -- expand the Lie derivative of the metric off the diagonal
  have hLg : lieDerivativeTensor I X (metricOperator g) ![U, V] p
      = directionalDerivative X (fun q => g.metricInner q (U q) (V q)) p
        - g.metricInner p (lieDerivativeVectorField I X U p) (V p)
        - g.metricInner p (U p) (lieDerivativeVectorField I X V p) := by
    rw [lieDerivativeTensor_formula, Fin.sum_univ_two]
    have h0 : (Function.update (![U, V]) (0 : Fin 2) (lieDerivativeVectorField I X U))
        = ![lieDerivativeVectorField I X U, V] := by
      funext j; fin_cases j <;> simp
    have h1 : (Function.update (![U, V]) (1 : Fin 2) (lieDerivativeVectorField I X V))
        = ![U, lieDerivativeVectorField I X V] := by
      funext j; fin_cases j <;> simp
    have hUV : (fun q => metricOperator g ![U, V] q)
        = fun q => g.metricInner q (U q) (V q) := by
      funext q; simp [metricOperator]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h0, h1,
      metricOperator_apply, hUV]
    ring
  -- metric compatibility along X
  have hcompat := D.metric_compat hU hV p (X p)
  rw [dirTangent_eq_directionalDerivative] at hcompat
  -- torsion-freeness on the two pairs: [X,U] = ∇_X U − ∇_U X, [X,V] = ∇_X V − ∇_V X
  have htfU := D.torsion_free hX hU p
  have htfV := D.torsion_free hX hV p
  rw [hLg, hcompat, ← htfU, ← htfV, g.metricInner_sub_left, g.metricInner_sub_right,
    g.metricInner_comm p (U p) (D.cov p (V p) X)]
  ring

/-- **Math.** For a **Killing field** `X` (`L_X g = 0`), the `(1,1)`-tensor
`S : V ↦ ∇_V X` is skew-symmetric with respect to `g`:
`g(∇_U X, V) = -g(∇_V X, U)`.  Immediate from the polarized covariant Killing
equation.  This is the fundamental pointwise characterization used throughout
Killing-field theory. -/
theorem IsKillingField.metricInner_cov_skew
    {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {X U V : Π x : M, TangentSpace I x} (hKill : IsKillingField g X)
    (hX : IsSmoothVectorField X) (hU : IsSmoothVectorField U)
    (hV : IsSmoothVectorField V) (p : M) :
    g.metricInner p (D.cov p (U p) X) (V p)
      = -g.metricInner p (D.cov p (V p) X) (U p) := by
  have h := D.metricInner_cov_add_swap_eq_lie hX hU hV p
  have hzero : lieDerivativeTensor I X (metricOperator g) ![U, V] p = 0 := by
    have hsm : ∀ i, IsSmoothVectorField (![U, V] i) := by
      intro i; fin_cases i <;> assumption
    exact congrFun (hKill ![U, V] hsm) p
  rw [hzero] at h
  linarith

/-! ## The covariant derivative of a dual `1`-form on the diagonal -/

/-- **Math.** For the dual `1`-form `θ_X = i_X g`,
`(∇_Y θ_X)(Y) = g(∇_Y X, Y)`: expanding the covariant derivative of the
`(0,1)`-tensor `θ_X` and cancelling the `g(X, ∇_Y Y)` term against metric
compatibility. -/
theorem covariantDerivativeTensor_dualOneForm_diag
    {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y) (p : M) :
    covariantDerivativeTensor D.toAffineConnection Y (dualOneForm g X) ![Y] p
      = g.metricInner p (D.cov p (Y p) X) (Y p) := by
  have hcompat := D.metric_compat hX hY p (Y p)
  rw [dirTangent_eq_directionalDerivative] at hcompat
  have hfun : (dualOneForm g X ![Y]) = (fun q => g.metricInner q (X q) (Y q)) := by
    funext q; simp [dualOneForm]
  rw [covariantDerivativeTensor_formula, Fin.sum_univ_one, hfun]
  simp only [Matrix.cons_val_zero, dualOneForm_apply, AffineConnection.covField_apply,
    Function.update_self]
  rw [hcompat]
  ring

/-! ## The adjoint of the covariant derivative -/

/-- **Math.** The **adjoint of the covariant derivative** (Petersen §2.2.4).
For a `(0, k+1)`-tensor `S` and an orthonormal frame `E₁, …, Eₙ`, the adjoint
`∇*S` is the `(0, k)`-tensor
`(∇*S)(X₂, …, X_t) = -Σᵢ (∇_{Eᵢ}S)(Eᵢ, X₂, …, X_t)`. -/
def covariantDerivativeAdjoint (D : AffineConnection I M) {ι : Type*} [Fintype ι]
    (Efr : ι → Π x : M, TangentSpace I x) {k : ℕ} (S : TensorOperator I M (k + 1)) :
    TensorOperator I M k :=
  fun Y => -∑ i, covariantDerivativeTensor D (Efr i) S (Fin.cons (Efr i) Y)

theorem covariantDerivativeAdjoint_apply (D : AffineConnection I M) {ι : Type*} [Fintype ι]
    (Efr : ι → Π x : M, TangentSpace I x) {k : ℕ} (S : TensorOperator I M (k + 1))
    (Y : Fin k → Π x : M, TangentSpace I x) (x : M) :
    covariantDerivativeAdjoint D Efr S Y x
      = -∑ i, covariantDerivativeTensor D (Efr i) S (Fin.cons (Efr i) Y) x := by
  simp only [covariantDerivativeAdjoint, Pi.neg_apply, Finset.sum_apply]

/-! ## Prop. 2.2.7 — divergence as the adjoint of the dual `1`-form -/

section Divergence

variable [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [hm : HasMetric I M]

/-- **Math.** **Prop. 2.2.7** (Petersen §2.2.4): the divergence of a vector
field is minus the adjoint of its dual `1`-form, `div X = -∇*θ_X`.  Stated
against a positively oriented orthonormal frame `Eᵢ` near `x` (orthonormal for
`g` and normalized `vol(E₁, …, Eₙ) = 1` on a neighborhood), matching the
standing frame hypothesis of the divergence. -/
theorem divergence_eq_neg_adjoint_dualForm
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (D : RiemannianConnection I hm.metric)
    {X : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    {Efr : Fin (finrank ℝ E) → Π x : M, TangentSpace I x}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) :
    divergenceLieDerivative o X x
      = -covariantDerivativeAdjoint D.toAffineConnection Efr (dualOneForm hm.metric X)
          ![] x := by
  rw [covariantDerivativeAdjoint_apply, neg_neg,
    divergence_trace_formula o X hEs hU horth hvol]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (Fin.cons (Efr i) (![] : Fin 0 → Π x : M, TangentSpace I x)) = ![Efr i] from rfl,
    covariantDerivativeTensor_dualOneForm_diag D hX (hEs i),
    RiemannianConnection.metricInner_cov_self_eq_half_lie D hX (hEs i)]

end Divergence

end PetersenLib
