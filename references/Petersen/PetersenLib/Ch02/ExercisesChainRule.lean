import PetersenLib.Ch02.VolumeDivergence

/-!
# Petersen Ch. 2, §2.5 — chain rules for the Hessian and Laplacian

Exercises 2.5.15 and 2.5.6: for `f : (M, g) → ℝ` and `φ : ℝ → ℝ`,

* `Hess(φ ∘ f) = φ'(f) · Hess f + φ''(f) · df ⊗ df` (Exercise 2.5.15);
* `Δ(φ ∘ f) = φ'(f) · Δf + φ''(f) · |df|²` together with the Hessian formula
  (Exercise 2.5.6).

The engine is the scaled-direction Lie-derivative formula
`lieDerivative_scale_direction` (Prop. 2.1.4) applied to `Hess f = ½ L_{∇f} g`
and the gradient chain rule `∇(φ ∘ f) = φ'(f) · ∇f`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Chain rule for the directional derivative against a real outer function -/

omit [IsManifold I ∞ M] in
/-- **Math.** Chain rule for the directional derivative through a real function
`ψ : ℝ → ℝ`: `D_Y(ψ ∘ f) = ψ'(f) · D_Y f`. -/
theorem directionalDerivative_comp_real {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) {ψ : ℝ → ℝ}
    (hψ : DifferentiableAt ℝ ψ (f x)) (Y : Π x : M, TangentSpace I x) :
    directionalDerivative Y (fun p => ψ (f p)) x
      = deriv ψ (f x) * directionalDerivative Y f x := by
  have hψm : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) ψ (f x) := hψ.mdifferentiableAt
  have hcomp : (fun p => ψ (f p)) = ψ ∘ f := rfl
  rw [directionalDerivative_apply, hcomp, mfderiv_comp x hψm hf,
    ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv, hψ.hasDerivAt.hasFDerivAt.fderiv]
  show (ContinuousLinearMap.toSpanSingleton ℝ (deriv ψ (f x))) (directionalDerivative Y f x)
      = deriv ψ (f x) * directionalDerivative Y f x
  rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]

/-! ## Chain rule for the gradient -/

variable [FiniteDimensional ℝ E]

/-- **Math.** Chain rule for the gradient through a real function `φ : ℝ → ℝ`:
`∇(φ ∘ f) = φ'(f) · ∇f`. -/
theorem gradient_comp_real {f : M → ℝ} (hf : ∀ x, MDifferentiableAt I 𝓘(ℝ) f x)
    {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) (g : RiemannianMetric I M) :
    gradient g (fun p => φ (f p)) = fun p => deriv φ (f p) • gradient g f p := by
  funext x
  refine (gradient_unique g (fun p => φ (f p)) x (deriv φ (f x) • gradient g f x)
    fun w => ?_).symm
  rw [g.metricInner_smul_left, metricInner_gradient]
  have := directionalDerivative_comp_real (I := I) (hf x) (hψ := hφ (f x)) (fun _ => w)
  simpa [directionalDerivative_apply] using this.symm

/-! ## Exercise 2.5.15 — chain rule for the Hessian -/

/-- **Math.** **Exercise 2.5.15** (Petersen §2.5): for `f : (M, g) → ℝ` with
smooth gradient and `φ : ℝ → ℝ` smooth,
`Hess(φ ∘ f) = φ'(f) · Hess f + φ''(f) · df ⊗ df`, evaluated on a pair `(Y₀, Y₁)`:
`Hess(φ∘f)(Y₀,Y₁) = φ'(f)·Hess f(Y₀,Y₁) + φ''(f)·df(Y₀)·df(Y₁)`.

Proof: the gradient chain rule `∇(φ∘f) = φ'(f)·∇f` reduces `Hess(φ∘f) =
½ L_{∇(φ∘f)} g` to the Lie derivative in the scaled direction `φ'(f)·∇f`; the
scaled-direction formula (Prop. 2.1.4) produces `φ'(f)·L_{∇f}g` plus the two
correction terms `D_{Yᵢ}(φ'(f))·g(∇f, Y_{1-i}) = φ''(f)·df(Yᵢ)·df(Y_{1-i})`. -/
theorem exercise2_5_15 [I.Boundaryless] [CompleteSpace E] {g : RiemannianMetric I M}
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hgradf : IsSmoothVectorField (gradient g f))
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (Y : Fin 2 → Π x : M, TangentSpace I x) (hY : ∀ i, IsSmoothVectorField (Y i)) (x : M) :
    hessianLieDerivative g (fun p => φ (f p)) Y x
      = deriv φ (f x) * hessianLieDerivative g f Y x
        + deriv (deriv φ) (f x)
            * (directionalDerivative (Y 0) f x * directionalDerivative (Y 1) f x) := by
  have hfd : ∀ x, MDifferentiableAt I 𝓘(ℝ) f x := fun x => (hf x).mdifferentiableAt (by decide)
  have hφdiff : Differentiable ℝ φ := hφ.differentiable (by decide)
  have hderivφ : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hderivφdiff : Differentiable ℝ (deriv φ) := hderivφ.differentiable (by decide)
  -- gradient chain rule
  have hgrad : gradient g (fun p => φ (f p)) = fun p => deriv φ (f p) • gradient g f p :=
    gradient_comp_real hfd hφdiff g
  -- smoothness of the scaling function `deriv φ ∘ f`
  have hscale : ContMDiff I 𝓘(ℝ) ∞ (fun p => deriv φ (f p)) :=
    hderivφ.contMDiff.comp hf
  -- the scaled-direction Lie-derivative formula (Prop. 2.1.4)
  have hLie := lieDerivative_scale_direction (metricOperator_isTensorOperator g)
    hgradf hscale Y hY x
  -- the two correction terms via the metric and the second directional chain rule
  have hM0 : metricOperator g (Function.update Y 0 (gradient g f)) x
      = directionalDerivative (Y 1) f x := by
    rw [metricOperator_apply, Function.update_self, Function.update_of_ne (by decide),
      metricInner_gradient]
    rfl
  have hM1 : metricOperator g (Function.update Y 1 (gradient g f)) x
      = directionalDerivative (Y 0) f x := by
    rw [metricOperator_apply, Function.update_of_ne (by decide), Function.update_self,
      g.metricInner_comm, metricInner_gradient]
    rfl
  have hD0 : directionalDerivative (Y 0) (fun p => deriv φ (f p)) x
      = deriv (deriv φ) (f x) * directionalDerivative (Y 0) f x :=
    directionalDerivative_comp_real (hfd x) (hderivφdiff (f x)) (Y 0)
  have hD1 : directionalDerivative (Y 1) (fun p => deriv φ (f p)) x
      = deriv (deriv φ) (f x) * directionalDerivative (Y 1) f x :=
    directionalDerivative_comp_real (hfd x) (hderivφdiff (f x)) (Y 1)
  -- assemble
  rw [hessianLieDerivative_apply, hgrad, hLie, hessianLieDerivative_apply g f,
    Fin.sum_univ_two, hM0, hM1, hD0, hD1]
  ring

/-! ## Exercise 2.5.6 — chain rules for the Laplacian and Hessian -/

/-- **Math.** **Exercise 2.5.6** (Petersen §2.5): for `f : (M, g) → ℝ` with
smooth gradient and `φ : ℝ → ℝ` smooth, on an oriented Riemannian manifold with a
positively oriented normalized orthonormal frame `Eᵢ` near `x`,
`Δ(φ∘f) = φ'(f)·Δf + φ''(f)·|df|²` (with `|df|² = Σᵢ df(Eᵢ)²` in the frame), and
`Hess(φ∘f) = φ'(f)·Hess f + φ''(f)·df⊗df`.

Proof: the Laplacian is the metric trace of the Hessian
(`laplacian_eq_hessian_trace`), so applying the Hessian chain rule
(`exercise2_5_15`) to each diagonal pair `(Eᵢ, Eᵢ)` and summing gives the
Laplacian formula; the Hessian formula is `exercise2_5_15` itself. -/
theorem exercise2_5_6 [I.Boundaryless] [CompleteSpace E] [InnerProductSpace ℝ E]
    [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [hm : HasMetric I M]
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (Module.finrank ℝ E)))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hgradf : IsSmoothVectorField (gradient hm.metric f))
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {Efr : Fin (Module.finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) :
    (laplacian o (fun p => φ (f p)) x
        = deriv φ (f x) * laplacian o f x
          + deriv (deriv φ) (f x) * ∑ i, directionalDerivative (Efr i) f x ^ 2)
      ∧ (∀ Y : Fin 2 → Π q : M, TangentSpace I q, (∀ i, IsSmoothVectorField (Y i)) →
          hessianLieDerivative hm.metric (fun p => φ (f p)) Y x
            = deriv φ (f x) * hessianLieDerivative hm.metric f Y x
              + deriv (deriv φ) (f x)
                  * (directionalDerivative (Y 0) f x * directionalDerivative (Y 1) f x)) := by
  refine ⟨?_, fun Y hY => exercise2_5_15 hf hgradf hφ Y hY x⟩
  rw [laplacian_eq_hessian_trace o (fun p => φ (f p)) hEs hU horth hvol,
    laplacian_eq_hessian_trace o f hEs hU horth hvol, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hYi : ∀ j,
      IsSmoothVectorField ((![Efr i, Efr i] : Fin 2 → Π q : M, TangentSpace I q) j) := by
    intro j; fin_cases j <;> exact hEs i
  rw [exercise2_5_15 hf hgradf hφ ![Efr i, Efr i] hYi x]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-! ## Prop. — the Hessian at a critical point depends on the metric only at `p` -/

/-- **Math.** **Hessian at a critical point is metric-independent** (Petersen
§2.1.3, `prop:pet-ch2-hessian-critical-point`): if `df|_p = 0`, then the Hessian
`Hess f = ½ L_{∇f} g` at `p` equals `½ L_{∇f} S` at `p` for *any* `(0,2)`-tensor
`S` agreeing with the metric at `p`.  In particular, taking `S` the flat metric
in coordinates with `g_{ij}|_p = δ_{ij}`, the Hessian at `p` coincides with the
one computed from the flat metric in those coordinates.

Proof: `df|_p = 0` gives `∇f|_p = 0`, so by locality of the Lie derivative at a
zero of the direction (Lem. 2.1.5, `lieDerivative_local_at_zero`) the value of
`L_{∇f}(·)|_p` depends only on the tensor's value at `p`, where `g` and `S`
agree. -/
theorem hessian_criticalPoint_metricIndependent (g : RiemannianMetric I M)
    {f : M → ℝ} {p : M} (hcrit : mfderiv I 𝓘(ℝ) f p = 0)
    (S : TensorOperator I M 2)
    (hSg : ∀ Z : Fin 2 → Π x : M, TangentSpace I x, S Z p = metricOperator g Z p)
    (Y : Fin 2 → Π x : M, TangentSpace I x) :
    hessianLieDerivative g f Y p
      = (1 / 2 : ℝ) * lieDerivativeTensor I (gradient g f) S Y p := by
  have hX : gradient g f p = 0 := by
    show g.metricRiesz p (mfderiv I 𝓘(ℝ) f p) = 0
    rw [hcrit]
    exact map_zero _
  rw [hessianLieDerivative_apply]
  congr 1
  exact lieDerivative_local_at_zero hX (fun Z => (hSg Z).symm) Y

end PetersenLib
