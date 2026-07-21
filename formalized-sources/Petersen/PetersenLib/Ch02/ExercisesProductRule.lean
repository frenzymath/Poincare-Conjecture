import PetersenLib.Ch02.ExercisesChainRule

/-!
# Petersen Ch. 2, §2.5 — product rules for divergence, Laplacian, Hessian

Exercise 2.5.5: for functions `f, h` and a vector field `X` on `(M, g)`,

* `div(f X) = D_X f + f · div X`;
* `Δ(f h) = h Δf + f Δh + 2 g(∇f, ∇h)`;
* `Hess(f h) = h Hess f + f Hess h + df ⊗ dh + dh ⊗ df`.

All three reduce to the scaled-direction Lie-derivative formula
`lieDerivative_scale_direction` (Prop. 2.1.4) via `Hess f = ½ L_{∇f} g`,
`Δ = tr Hess`, and the gradient product rule `∇(f h) = h ∇f + f ∇h`. The new
building blocks are the direction-additivity of the Lie derivative
(`lieDerivativeTensor_add_direction`), the gradient product rule
(`gradient_mul`), and the orthonormal-frame polarization identity
`Σᵢ g(u, Eᵢ) g(w, Eᵢ) = g(u, w)` (`metricInner_orthonormal_polarization`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Direction-additivity of the Lie derivative of a tensor -/

/-- **Math.** The Lie derivative of a `(0,k)`-tensor is additive in the
differentiating direction: `L_{X+X'} T = L_X T + L_{X'} T`. -/
theorem lieDerivativeTensor_add_direction [CompleteSpace E] {k : ℕ}
    {T : TensorOperator I M k}
    (hT : IsTensorOperator T) {X X' : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hX' : IsSmoothVectorField X')
    (Y : Fin k → Π x : M, TangentSpace I x) (x : M) :
    lieDerivativeTensor I (fun p => X p + X' p) T Y x
      = lieDerivativeTensor I X T Y x + lieDerivativeTensor I X' T Y x := by
  have hbr : ∀ i, lieDerivativeVectorField I (fun p => X p + X' p) (Y i)
      = fun p => lieDerivativeVectorField I X (Y i) p
        + lieDerivativeVectorField I X' (Y i) p := by
    intro i
    funext p
    have hXd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun q => (⟨q, X q⟩ : TangentBundle I M)) p := (hX p).mdifferentiableAt (by decide)
    have hX'd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun q => (⟨q, X' q⟩ : TangentBundle I M)) p := (hX' p).mdifferentiableAt (by decide)
    have hsm : (fun p => X p + X' p) = X + X' := rfl
    rw [lieDerivativeVectorField_eq_mlieBracket, hsm,
      VectorField.mlieBracket_add_left hXd hX'd]
    rfl
  rw [lieDerivativeTensor_formula, lieDerivativeTensor_formula, lieDerivativeTensor_formula,
    directionalDerivative_add_left]
  have hsum : ∑ i, T (Function.update Y i
        (lieDerivativeVectorField I (fun p => X p + X' p) (Y i))) x
      = ∑ i, T (Function.update Y i (lieDerivativeVectorField I X (Y i))) x
        + ∑ i, T (Function.update Y i (lieDerivativeVectorField I X' (Y i))) x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IsTensorOperator.congr_slot (T := T) (hbr i), hT.add_slot]
  rw [hsum]
  abel

/-- Smoothness of a smooth-scalar multiple of a smooth vector field. -/
theorem isSmoothVectorField_smul {c : M → ℝ} (hc : ContMDiff I 𝓘(ℝ) ∞ c)
    {V : Π x : M, TangentSpace I x} (hV : IsSmoothVectorField V) :
    IsSmoothVectorField (fun p => c p • V p) :=
  ContMDiff.smul_section hc hV

/-! ## Gradient product rule -/

variable [FiniteDimensional ℝ E]

/-- **Math.** Product rule for the gradient: `∇(f h) = h ∇f + f ∇h`. -/
theorem gradient_mul {f h : M → ℝ} (hf : ∀ x, MDifferentiableAt I 𝓘(ℝ) f x)
    (hh : ∀ x, MDifferentiableAt I 𝓘(ℝ) h x) (g : RiemannianMetric I M) :
    gradient g (fun p => f p * h p)
      = fun p => h p • gradient g f p + f p • gradient g h p := by
  funext x
  refine (gradient_unique g (fun p => f p * h p) x
    (h x • gradient g f x + f x • gradient g h x) fun w => ?_).symm
  rw [g.metricInner_add_left, g.metricInner_smul_left, g.metricInner_smul_left,
    metricInner_gradient, metricInner_gradient]
  have hmul := directionalDerivative_mul (I := I) (hf x) (hh x) (fun _ => w)
  simp only [directionalDerivative_apply] at hmul
  rw [show (fun p => f p * h p) = f * h from rfl, hmul]; ring

/-! ## Hessian product rule (Hessian half of Exercise 2.5.5) -/

/-- **Math.** Product rule for the Hessian (Petersen §2.5, Exercise 2.5.5):
`Hess(f h)(Y₀, Y₁) = h·Hess f + f·Hess h + df(Y₀)dh(Y₁) + dh(Y₀)df(Y₁)`. -/
theorem hessianLieDerivative_mul [I.Boundaryless] [CompleteSpace E]
    {g : RiemannianMetric I M} {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ) ∞ h)
    (hgradf : IsSmoothVectorField (gradient g f))
    (hgradh : IsSmoothVectorField (gradient g h))
    (Y : Fin 2 → Π x : M, TangentSpace I x) (hY : ∀ i, IsSmoothVectorField (Y i)) (x : M) :
    hessianLieDerivative g (fun p => f p * h p) Y x
      = h x * hessianLieDerivative g f Y x + f x * hessianLieDerivative g h Y x
        + (directionalDerivative (Y 0) f x * directionalDerivative (Y 1) h x
          + directionalDerivative (Y 0) h x * directionalDerivative (Y 1) f x) := by
  have hfd : ∀ x, MDifferentiableAt I 𝓘(ℝ) f x := fun x => (hf x).mdifferentiableAt (by decide)
  have hhd : ∀ x, MDifferentiableAt I 𝓘(ℝ) h x := fun x => (hh x).mdifferentiableAt (by decide)
  -- correction terms via the metric and the gradient property
  have hMf0 : metricOperator g (Function.update Y 0 (gradient g f)) x
      = directionalDerivative (Y 1) f x := by
    rw [metricOperator_apply, Function.update_self, Function.update_of_ne (by decide),
      metricInner_gradient]; rfl
  have hMf1 : metricOperator g (Function.update Y 1 (gradient g f)) x
      = directionalDerivative (Y 0) f x := by
    rw [metricOperator_apply, Function.update_of_ne (by decide), Function.update_self,
      g.metricInner_comm, metricInner_gradient]; rfl
  have hMh0 : metricOperator g (Function.update Y 0 (gradient g h)) x
      = directionalDerivative (Y 1) h x := by
    rw [metricOperator_apply, Function.update_self, Function.update_of_ne (by decide),
      metricInner_gradient]; rfl
  have hMh1 : metricOperator g (Function.update Y 1 (gradient g h)) x
      = directionalDerivative (Y 0) h x := by
    rw [metricOperator_apply, Function.update_of_ne (by decide), Function.update_self,
      g.metricInner_comm, metricInner_gradient]; rfl
  rw [hessianLieDerivative_apply, gradient_mul hfd hhd g,
    lieDerivativeTensor_add_direction (metricOperator_isTensorOperator g)
      (isSmoothVectorField_smul hh hgradf) (isSmoothVectorField_smul hf hgradh) Y x,
    lieDerivative_scale_direction (metricOperator_isTensorOperator g) hgradf hh Y hY x,
    lieDerivative_scale_direction (metricOperator_isTensorOperator g) hgradh hf Y hY x,
    hessianLieDerivative_apply g f, hessianLieDerivative_apply g h,
    Fin.sum_univ_two, Fin.sum_univ_two, hMf0, hMf1, hMh0, hMh1]
  ring

/-! ## Orthonormal-frame polarization -/

section Frame

variable [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [hm : HasMetric I M]

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
/-- **Math.** Polarization in a `g`-orthonormal frame:
`Σᵢ g(u, Eᵢ)·g(w, Eᵢ) = g(u, w)`. -/
theorem metricInner_orthonormal_polarization {y : M}
    {v : Fin (Module.finrank ℝ E) → TangentSpace I y}
    (h : ∀ i j, hm.metric.metricInner y (v i) (v j) = if i = j then 1 else 0)
    (u w : TangentSpace I y) :
    ∑ i, hm.metric.metricInner y u (v i) * hm.metric.metricInner y w (v i)
      = hm.metric.metricInner y u w := by
  conv_rhs => rw [metricInner_orthonormal_expansion h w]
  simp only [hasMetric_metricInner_eq_inner, inner_sum, real_inner_smul_right]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ## Divergence product rule (divergence half of Exercise 2.5.5) -/

variable [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Product rule for the divergence (Petersen §2.5, Exercise 2.5.5):
`div(f X) = D_X f + f · div X`, against a positively oriented normalized
orthonormal frame near `x`. -/
theorem divergence_smul
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (Module.finrank ℝ E)))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    {Efr : Fin (Module.finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) :
    divergenceLieDerivative o (fun p => f p • X p) x
      = directionalDerivative X f x + f x * divergenceLieDerivative o X x := by
  have hYi : ∀ i, ∀ j,
      IsSmoothVectorField ((![Efr i, Efr i] : Fin 2 → Π q : M, TangentSpace I q) j) := by
    intro i j; fin_cases j <;> exact hEs i
  -- per-frame-index expansion of the scaled Lie derivative via Prop. 2.1.4
  have hterm : ∀ i, (1 / 2 : ℝ)
      * lieDerivativeTensor I (fun p => f p • X p) (metricOperator hm.metric)
          ![Efr i, Efr i] x
      = directionalDerivative (Efr i) f x
          * hm.metric.metricInner x (gradient hm.metric f x) (Efr i x) * 0
        + directionalDerivative (Efr i) f x * hm.metric.metricInner x (X x) (Efr i x)
        + f x * ((1 / 2 : ℝ)
            * lieDerivativeTensor I X (metricOperator hm.metric) ![Efr i, Efr i] x) := by
    intro i
    rw [lieDerivative_scale_direction (metricOperator_isTensorOperator hm.metric) hX hf
      ![Efr i, Efr i] (hYi i) x, Fin.sum_univ_two]
    have hu0 : metricOperator hm.metric (Function.update ![Efr i, Efr i] 0 X) x
        = hm.metric.metricInner x (X x) (Efr i x) := by
      rw [metricOperator_apply, Function.update_self, Function.update_of_ne (by decide)]
      simp
    have hu1 : metricOperator hm.metric (Function.update ![Efr i, Efr i] 1 X) x
        = hm.metric.metricInner x (X x) (Efr i x) := by
      rw [metricOperator_apply, Function.update_of_ne (by decide), Function.update_self,
        hm.metric.metricInner_comm]
      simp
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hu0, hu1]
    ring
  rw [divergence_trace_formula o (fun p => f p • X p) hEs hU horth hvol,
    divergence_trace_formula o X hEs hU horth hvol,
    Finset.sum_congr rfl (fun i _ => hterm i)]
  simp only [mul_zero, zero_add]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  -- Σᵢ D_{Eᵢ}f · g(X, Eᵢ) = D_X f, via polarization and the gradient property
  have hpol : ∑ i, hm.metric.metricInner x (gradient hm.metric f x) (Efr i x)
        * hm.metric.metricInner x (X x) (Efr i x)
      = hm.metric.metricInner x (gradient hm.metric f x) (X x) :=
    metricInner_orthonormal_polarization (horth x (mem_of_mem_nhds hU)) _ _
  rw [directionalDerivative_eq_metricInner_gradient hm.metric]
  rw [← hpol]
  exact Finset.sum_congr rfl fun i _ => by
    rw [directionalDerivative_eq_metricInner_gradient hm.metric]

/-! ## Laplacian product rule (Laplacian half of Exercise 2.5.5) -/

/-- **Math.** Product rule for the Laplacian (Petersen §2.5, Exercise 2.5.5):
`Δ(f h) = h Δf + f Δh + 2 g(∇f, ∇h)`, against a positively oriented normalized
orthonormal frame near `x`. -/
theorem laplacian_mul
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (Module.finrank ℝ E)))
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ) ∞ h)
    (hgradf : IsSmoothVectorField (gradient hm.metric f))
    (hgradh : IsSmoothVectorField (gradient hm.metric h))
    {Efr : Fin (Module.finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) :
    laplacian o (fun p => f p * h p) x
      = h x * laplacian o f x + f x * laplacian o h x
        + 2 * hm.metric.metricInner x (gradient hm.metric f x) (gradient hm.metric h x) := by
  have hYi : ∀ i, ∀ j,
      IsSmoothVectorField ((![Efr i, Efr i] : Fin 2 → Π q : M, TangentSpace I q) j) := by
    intro i j; fin_cases j <;> exact hEs i
  have hHess : ∀ i,
      hessianLieDerivative hm.metric (fun p => f p * h p) ![Efr i, Efr i] x
      = h x * hessianLieDerivative hm.metric f ![Efr i, Efr i] x
        + f x * hessianLieDerivative hm.metric h ![Efr i, Efr i] x
        + 2 * (directionalDerivative (Efr i) f x * directionalDerivative (Efr i) h x) := by
    intro i
    rw [hessianLieDerivative_mul hf hh hgradf hgradh ![Efr i, Efr i] (hYi i) x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hpolfh : ∑ i, directionalDerivative (Efr i) f x * directionalDerivative (Efr i) h x
      = hm.metric.metricInner x (gradient hm.metric f x) (gradient hm.metric h x) := by
    rw [← metricInner_orthonormal_polarization (horth x (mem_of_mem_nhds hU))
        (gradient hm.metric f x) (gradient hm.metric h x)]
    exact Finset.sum_congr rfl fun i _ => by
      rw [directionalDerivative_eq_metricInner_gradient hm.metric,
        directionalDerivative_eq_metricInner_gradient hm.metric]
  rw [laplacian_eq_hessian_trace o (fun p => f p * h p) hEs hU horth hvol,
    laplacian_eq_hessian_trace o f hEs hU horth hvol,
    laplacian_eq_hessian_trace o h hEs hU horth hvol,
    Finset.sum_congr rfl (fun i _ => hHess i), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hpolfh]

/-! ## Exercise 2.5.5 — all three product rules -/

/-- **Math.** **Exercise 2.5.5** (Petersen §2.5): for functions `f, h` and a
vector field `X` on `(M, g)`, against a positively oriented normalized
orthonormal frame near `x`,
`div(f X) = D_X f + f · div X`, `Δ(f h) = h Δf + f Δh + 2 g(∇f, ∇h)`, and
`Hess(f h) = h Hess f + f Hess h + df ⊗ dh + dh ⊗ df`. -/
theorem exercise2_5_5
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (Module.finrank ℝ E)))
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ) ∞ h)
    {X : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    (hgradf : IsSmoothVectorField (gradient hm.metric f))
    (hgradh : IsSmoothVectorField (gradient hm.metric h))
    {Efr : Fin (Module.finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) :
    (divergenceLieDerivative o (fun p => f p • X p) x
        = directionalDerivative X f x + f x * divergenceLieDerivative o X x)
      ∧ (laplacian o (fun p => f p * h p) x
          = h x * laplacian o f x + f x * laplacian o h x
            + 2 * hm.metric.metricInner x (gradient hm.metric f x) (gradient hm.metric h x))
      ∧ (∀ Y : Fin 2 → Π q : M, TangentSpace I q, (∀ i, IsSmoothVectorField (Y i)) →
          hessianLieDerivative hm.metric (fun p => f p * h p) Y x
            = h x * hessianLieDerivative hm.metric f Y x
              + f x * hessianLieDerivative hm.metric h Y x
              + (directionalDerivative (Y 0) f x * directionalDerivative (Y 1) h x
                + directionalDerivative (Y 0) h x * directionalDerivative (Y 1) f x)) :=
  ⟨divergence_smul o hf hX hEs hU horth hvol,
    laplacian_mul o hf hh hgradf hgradh hEs hU horth hvol,
    fun Y hY => hessianLieDerivative_mul hf hh hgradf hgradh Y hY x⟩

end Frame

end PetersenLib
