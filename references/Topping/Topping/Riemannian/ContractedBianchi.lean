import Topping.Riemannian.SmoothTensor
import Topping.Riemannian.VariationScalar

/-!
# The contracted Bianchi identity, `δG(\Ric) = 0`

Topping's background remark closes with the contracted second Bianchi identity in
the form he uses throughout:

`δG(\Ric) = δ\Ric + ½dR = 0`,

where `G(T) = T - ½(\tr T)g` is the gravitation tensor and `δ = -\tr₁₂∇`. This
module proves it, and the proof is short because both halves are already
available in the workspace under different names:

* `δ\Ric = -½dR` is `divergence_ricciTensorField`, which is Morgan--Tian's
  `dR = 2\,\mathrm{div}(\Ric)` (their Lemma 1.9, itself the double contraction of
  the second Bianchi identity) read through Topping's sign convention `δ = -\tr₁₂∇`;
* `δ(½Rg) = -½dR` needs `∇g = 0`. That is not bookkeeping: metric compatibility
  of the Levi-Civita connection is *exactly* the statement that the Leibniz
  correction defining `∇_Xg` cancels the derivative of `g(Y,Z)`, which is
  `covDerivAlong_metricTensorField_eq_zero` below.

Adding the two gives `0`, which is the identity. The two `½dR`'s cancelling is
the reason `G` is the right object: the same cancellation is what makes `G(\Ric)`
divergence-free and hence what makes the Einstein tensor the natural
divergence-free curvature quantity.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### `∇g = 0` -/

omit [I.Boundaryless] in
/-- **Math.** The metric is covariantly constant, `∇_Xg = 0`. This is metric
compatibility of the Levi-Civita connection restated as the vanishing of a
covariant derivative: `(∇_Xg)(Y,Z) = X⟨Y,Z⟩ - ⟨∇_XY,Z⟩ - ⟨Y,∇_XZ⟩`, and
compatibility says precisely that the first term is the sum of the other two. -/
theorem covDerivAlong_metricTensorField_eq_zero (g : RiemannianMetric I M)
    (X : SmoothVectorField I M) (Y : Fin 2 → SmoothVectorField I M) (p : M) :
    covDerivAlong g.leviCivitaConnection X (metricTensorField g) Y p = 0 := by
  have hcompat := (isLeviCivita_leviCivitaConnection g).2 X (Y 0) (Y 1) p
  rw [covDerivAlong_apply]
  -- The two Leibniz corrections update slot `0` and slot `1` respectively.
  rw [Fin.sum_univ_two]
  have h0 : metricTensorField g
      (Function.update Y 0 (g.leviCivitaConnection.cov X (Y 0))) p
      = g.metricInner p ((g.leviCivitaConnection.cov X (Y 0)) p) (Y 1 p) := by
    rw [metricTensorField, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  have h1 : metricTensorField g
      (Function.update Y 1 (g.leviCivitaConnection.cov X (Y 1))) p
      = g.metricInner p (Y 0 p) ((g.leviCivitaConnection.cov X (Y 1)) p) := by
    rw [metricTensorField, Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  rw [h0, h1, show metricTensorField g Y
      = fun q => g.metricInner q (Y 0 q) (Y 1 q) from rfl, hcompat]
  ring

/-! ### The divergence of a function times the metric -/

omit [I.Boundaryless] in
/-- **Math.** `δ(fg) = -df` for a smooth function `f`: since `∇g = 0`, the only
contribution to `∇(fg)` is `df ⊗ g`, and tracing the derivative slot against the
first metric slot returns `df` — with a sign from `δ = -\tr₁₂∇`.

This is the step where covariant constancy of the metric does real work: without
it there would be a second term, and the cancellation defining `δG` would fail. -/
theorem divergence_smul_metricTensorField (g : RiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (Z : SmoothVectorField I M)
    (p : M) :
    divergence g g.leviCivitaConnection
        (fun (Y : Fin 2 → SmoothVectorField I M) q => f q * metricTensorField g Y q)
        (fun _ => Z) p
      = -Z.dir f p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with he
  rw [divergence_apply]
  -- Each summand is `(∇_{eᵢ}(fg))(eᵢ, Z) = (eᵢf)·g(eᵢ,Z)`, by `∇g = 0`.
  have hterm : ∀ i, covDerivAlong g.leviCivitaConnection
      (MorganTianLib.extendVector p (e i))
      (fun (Y : Fin 2 → SmoothVectorField I M) q => f q * metricTensorField g Y q)
      (Fin.cons (MorganTianLib.extendVector p (e i)) (fun _ => Z)) p
      = (MorganTianLib.extendVector p (e i)).dir f p *
        g.metricInner p (e i) (Z p) := by
    intro i
    set X := MorganTianLib.extendVector p (e i) with hX
    set Y : Fin 2 → SmoothVectorField I M :=
      Fin.cons X (fun _ => Z) with hY
    -- Leibniz for the product `f·g`, then `∇_Xg = 0` kills the second half.
    have hprod : covDerivAlong g.leviCivitaConnection X
        (fun (W : Fin 2 → SmoothVectorField I M) q => f q * metricTensorField g W q)
        Y p
        = X.dir f p * metricTensorField g Y p
          + f p * covDerivAlong g.leviCivitaConnection X (metricTensorField g) Y p := by
      simp only [covDerivAlong_apply]
      rw [show (fun q => f q * metricTensorField g Y q)
          = fun q => f q * g.metricInner q (Y 0 q) (Y 1 q) from rfl,
        show metricTensorField g Y
          = fun q => g.metricInner q (Y 0 q) (Y 1 q) from rfl]
      rw [X.dir_mul p (hf.mdifferentiable (by norm_num) p)
        ((g.metricInner_field_contMDiff (Y 0) (Y 1)).mdifferentiable
          (by norm_num) p)]
      rw [← Finset.mul_sum]
      ring
    rw [hprod, covDerivAlong_metricTensorField_eq_zero]
    rw [metricTensorField, hY]
    simp only [Fin.cons_zero, Fin.cons_one, hX,
      MorganTianLib.extendVector_apply]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  -- `Σᵢ (eᵢf)·⟨eᵢ,Z⟩ = Zf`: each factor `eᵢf` is `⟨∇f,eᵢ⟩`, so the sum is the
  -- orthonormal expansion of `⟨∇f,Z⟩ = Zf`.
  have hgrad : ∀ i, (MorganTianLib.extendVector p (e i)).dir f p
      = inner ℝ (MorganTianLib.gradientField g f hf p) (e i) := fun i => by
    rw [← MorganTianLib.metricInner_gradientField_eq_dir g hf
      (MorganTianLib.extendVector p (e i)) p, MorganTianLib.extendVector_apply]
    rfl
  have hZ : g.metricInner p (MorganTianLib.gradientField g f hf p) (Z p)
      = Z.dir f p := MorganTianLib.metricInner_gradientField_eq_dir g hf Z p
  rw [Finset.sum_congr rfl fun i _ => by
    rw [hgrad i, show g.metricInner p (e i) (Z p)
      = inner ℝ (e i : TangentSpace I p) (Z p) from rfl]]
  rw [(stdOrthonormalBasis ℝ (TangentSpace I p)).sum_inner_mul_inner
    (MorganTianLib.gradientField g f hf p) (Z p), ← hZ]
  rfl

/-! ### Two pieces of linearity -/

/-- **Math.** `\tr\Ric = R`: the metric trace of the Ricci tensor field is the
scalar curvature. This is `scalarCurvatureAt`'s definition read through the
tensor-field trace, which feeds the two slots `extendVector`s of an orthonormal
basis. -/
theorem trace₂_ricciTensorField (g : RiemannianMetric I M) (q : M) :
    trace₂ g (ricciTensorField g) q = scalarCurvatureAt g q := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [trace₂, traceFirstTwo, scalarCurvatureAt_eq_trace,
    Riemannian.bilinTrace_eq_sum _ (stdOrthonormalBasis ℝ (TangentSpace I q))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ricciTensorField]
  simp only [Fin.cons_zero, Fin.cons_one, MorganTianLib.extendVector_apply]

omit [I.Boundaryless] in
/-- **Math.** The divergence is additive over differences, `δ(A - B) = δA - δB`,
given differentiable components: both the Leibniz derivative and the metric trace
defining `δ` are linear. -/
theorem divergence_sub (g : RiemannianMetric I M) {k : ℕ}
    {A B : CovTensorField I M (k + 1)}
    (hA : ∀ (Y : Fin (k + 1) → SmoothVectorField I M) (q : M),
      MDifferentiableAt I 𝓘(ℝ, ℝ) (A Y) q)
    (hB : ∀ (Y : Fin (k + 1) → SmoothVectorField I M) (q : M),
      MDifferentiableAt I 𝓘(ℝ, ℝ) (B Y) q)
    (Y : Fin k → SmoothVectorField I M) (p : M) :
    divergence g g.leviCivitaConnection
        (fun (W : Fin (k + 1) → SmoothVectorField I M) q => A W q - B W q) Y p
      = divergence g g.leviCivitaConnection A Y p
        - divergence g g.leviCivitaConnection B Y p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  -- `∇` itself is additive over the difference; then so is its trace.
  have hcov : ∀ (X : SmoothVectorField I M)
      (W : Fin (k + 1) → SmoothVectorField I M),
      covDerivAlong g.leviCivitaConnection X
          (fun (V : Fin (k + 1) → SmoothVectorField I M) q => A V q - B V q) W p
        = covDerivAlong g.leviCivitaConnection X A W p
          - covDerivAlong g.leviCivitaConnection X B W p := by
    intro X W
    simp only [covDerivAlong_apply]
    have hsub : (fun q => A W q - B W q)
        = fun q => A W q + (-1 : ℝ) * B W q := by funext q; ring
    have hnegB : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun q => (-1 : ℝ) * B W q) p :=
      (mdifferentiableAt_const (c := (-1 : ℝ))).mul (hB W p)
    rw [hsub, X.dir_add p (hA W p) hnegB,
      X.dir_const_mul (-1 : ℝ) p (hB W p), Finset.sum_sub_distrib]
    ring
  simp only [divergence_apply, hcov]
  rw [Finset.sum_sub_distrib]
  ring

/-! ### The identity -/

/-- **Math.** **The contracted Bianchi identity, `δG(\Ric) = δ\Ric + ½dR = 0`.**
Topping's form of the identity, and the last display of his background remark.

Both equalities are proved. The first is the definition of `G` unwound: the trace
of `\Ric` is `R`, so `δG(\Ric) = δ\Ric - δ(½Rg)`, and `δ(½Rg) = -½dR` by
`divergence_smul_metricTensorField` — the step that consumes `∇g = 0`. The second
is `δ\Ric = -½dR`, which is the contracted second Bianchi identity itself
(Morgan--Tian's Lemma 1.9 in Topping's sign convention). The two `½dR` cancel.

This is why `G` is the right object to state the identity with: `G(\Ric)` — the
Einstein tensor — is divergence-free, whereas `\Ric` alone is not. -/
theorem divergence_gravitationTensor_ricciTensorField (g : RiemannianMetric I M)
    (Z : SmoothVectorField I M) (p : M) :
    divergence g g.leviCivitaConnection
        (gravitationTensor g (ricciTensorField g)) (fun _ => Z) p = 0 := by
  -- `R` is smooth, which `δ(Rg)` needs.
  have hR : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => scalarCurvatureAt g q) := by
    have hfun : (fun q => scalarCurvatureAt g q)
        = MorganTianLib.scalarCurvatureAt g g.leviCivitaConnection
            (isLeviCivita_leviCivitaConnection g) :=
      funext fun q => scalarCurvatureAt_eq_scalarCurvatureAt g q
    rw [hfun]
    exact MorganTianLib.scalarCurvatureAt_contMDiff g g.leviCivitaConnection
      (isLeviCivita_leviCivitaConnection g)
  -- `G(\Ric) = \Ric - (½R)g`, as tensor fields.
  have hG : gravitationTensor g (ricciTensorField g)
      = fun (Y : Fin 2 → SmoothVectorField I M) q =>
        ricciTensorField g Y q
          - ((fun r => (1 / 2 : ℝ) * scalarCurvatureAt g r) q
            * metricTensorField g Y q) := by
    funext Y q
    rw [gravitationTensor, trace₂_ricciTensorField]
  -- The second summand is `f·g` for the smooth function `f = ½R`.
  have hhalf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => (1 / 2 : ℝ) * scalarCurvatureAt g q) :=
    contMDiff_const.mul hR
  rw [show gravitationTensor g (ricciTensorField g)
      = fun (Y : Fin 2 → SmoothVectorField I M) q =>
        ricciTensorField g Y q
          - ((fun r => (1 / 2 : ℝ) * scalarCurvatureAt g r) q
            * metricTensorField g Y q) from hG]
  -- `δ` splits over the difference, then both halves are `-½dR` and cancel.
  rw [divergence_sub g (A := ricciTensorField g)
      (B := fun (W : Fin 2 → SmoothVectorField I M) q =>
        (fun r => (1 / 2 : ℝ) * scalarCurvatureAt g r) q * metricTensorField g W q)
      (hasSmoothComponents_ricciTensorField g).mdifferentiableAt
      (fun W q => ((hhalf.mul
        (g.metricInner_field_contMDiff (W 0) (W 1))).mdifferentiable
          (by norm_num)) q)]
  rw [divergence_ricciTensorField,
    divergence_smul_metricTensorField g hhalf Z p]
  rw [Z.dir_const_mul (1 / 2 : ℝ) p ((hR.mdifferentiable (by norm_num)) p)]
  ring

end Topping

end
