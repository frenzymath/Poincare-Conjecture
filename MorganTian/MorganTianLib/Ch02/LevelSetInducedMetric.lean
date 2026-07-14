import MorganTianLib.Ch02.LevelSetChartedSpace
import MorganTianLib.Ch02.CurveAcceleration
import OpenGALib.Riemannian.Manifold.DoCarmoCh1

/-!
# Morgan–Tian Ch. 2 — the induced Riemannian metric on a level set

The regular level set `N_c = f⁻¹(c)` of a smooth function `f : M → ℝ` (with `df`
nowhere zero on `N_c`) is a smooth embedded hypersurface
(`LevelSetChartedSpace`).  Being the image of a smooth **immersion**
`ι = (·) : N_c → M` (`contMDiff_levelSet_val`, `mfderiv_levelSet_val_injective`),
`N_c` carries the **induced Riemannian metric** `g_{N_c}` — the pullback
`⟨v, w⟩_{g_{N_c}} = ⟨dι v, dι w⟩_g` of the ambient metric through the inclusion
differential.  This is do Carmo Ch. 1 Ex. 2.5, packaged by
`Riemannian.DCInducedMetric`.

This is the induced metric `g_{N_c}` of blueprint
`lem:parallel-gradient-level-sets`, the object on which the totally-geodesic
clause (item 3) and the Riemannian form of the Cheeger–Gromoll splitting
(`prop:parallel-gradient-splitting`) both rest.
-/

open Set Riemannian
open scoped Manifold Topology ContDiff

noncomputable section

namespace MorganTianLib

section ProductMetricSplit
variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]

/-- **Math.** The **product metric splits on split tangent vectors**: at
`(p₁, p₂) ∈ M₁ × M₂`, `⟨(u₁,u₂),(u₁',u₂')⟩_{g₁⊕g₂} = ⟨u₁,u₁'⟩_{g₁} + ⟨u₂,u₂'⟩_{g₂}`.
The evaluation form of do Carmo's `DCProductMetric` (its inner product is the sum
of the two factor pullbacks, and `dπᵢ (u₁,u₂) = uᵢ`). -/
theorem DCProductMetric_metricInner_mk (g₁ : RiemannianMetric I₁ M₁)
    (g₂ : RiemannianMetric I₂ M₂) (p₁ : M₁) (p₂ : M₂)
    (u₁ u₁' : TangentSpace I₁ p₁) (u₂ u₂' : TangentSpace I₂ p₂) :
    (DCProductMetric g₁ g₂).metricInner (p₁, p₂) (u₁, u₂) (u₁', u₂')
      = g₁.metricInner p₁ u₁ u₁' + g₂.metricInner p₂ u₂ u₂' := by
  show DCProductForm g₁ g₂ (p₁, p₂) (u₁, u₂) (u₁', u₂') = _
  rw [DCProductForm, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    DCInducedForm_apply, DCInducedForm_apply]
  have e1 : mfderiv (I₁.prod I₂) I₁ Prod.fst (p₁, p₂) (u₁, u₂) = u₁ := by rw [mfderiv_fst]; rfl
  have e1' : mfderiv (I₁.prod I₂) I₁ Prod.fst (p₁, p₂) (u₁', u₂') = u₁' := by rw [mfderiv_fst]; rfl
  have e2 : mfderiv (I₁.prod I₂) I₂ Prod.snd (p₁, p₂) (u₁, u₂) = u₂ := by rw [mfderiv_snd]; rfl
  have e2' : mfderiv (I₁.prod I₂) I₂ Prod.snd (p₁, p₂) (u₁', u₂') = u₂' := by rw [mfderiv_snd]; rfl
  rw [e1, e1', e2, e2']

end ProductMetricSplit

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]
  {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
  (c : ℝ)

/-- **Math.** The **induced Riemannian metric** `g_{N_c}` on the regular level
set `N_c = f⁻¹(c)`: the pullback of the ambient metric `g` through the smooth
immersion `ι : N_c → M`, `⟨v, w⟩_{g_{N_c}} = ⟨dι v, dι w⟩_g`.  Blueprint
`lem:parallel-gradient-level-sets`: the induced Riemannian metric on the
level set. -/
def levelSetInducedMetric (g : RiemannianMetric I M)
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    letI := levelSetChartedSpace hf n c hreg
    letI := isManifold_levelSet hf n c hreg
    RiemannianMetric (𝓡 n) (f ⁻¹' {c} : Set M) :=
  letI := levelSetChartedSpace hf n c hreg
  letI := isManifold_levelSet hf n c hreg
  DCInducedMetric (I := 𝓡 n) (I' := I) g ((↑) : (f ⁻¹' {c} : Set M) → M)
    ⟨contMDiff_levelSet_val hf n c hreg,
      fun p => mfderiv_levelSet_val_injective hf n c hreg p⟩

/-- **Math.** The induced metric is the pullback: `⟨v, w⟩_{g_{N_c}} =
⟨dι v, dι w⟩_g`, where `ι : N_c → M` is the inclusion and `dι` its differential.
This is the defining identity of `levelSetInducedMetric`. -/
theorem levelSetInducedMetric_metricInner (g : RiemannianMetric I M)
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (y : (f ⁻¹' {c} : Set M))
    (v w : letI := levelSetChartedSpace hf n c hreg; TangentSpace (𝓡 n) y) :
    letI := levelSetChartedSpace hf n c hreg
    letI := isManifold_levelSet hf n c hreg
    (levelSetInducedMetric hf n c g hreg).metricInner y v w
      = g.metricInner (↑y)
          (mfderiv (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) y v)
          (mfderiv (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) y w) := by
  letI := levelSetChartedSpace hf n c hreg
  letI := isManifold_levelSet hf n c hreg
  exact DCInducedForm_apply g _ y v w

/-- **Math.** The inclusion `ι : N_c → M` is an **isometric immersion**: it
preserves the metric, `⟨dι v, dι w⟩_g = ⟨v, w⟩_{g_{N_c}}` (the reverse reading
of `levelSetInducedMetric_metricInner`).  Together with
`range_mfderiv_levelSet_val` (`range dι = ker dB`) this says `dι` maps
`T_yN_c` isometrically onto the level-tangent hyperplane `ker dB_{ιy}`. -/
theorem metricInner_mfderiv_levelSet_val (g : RiemannianMetric I M)
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (y : (f ⁻¹' {c} : Set M))
    (v w : letI := levelSetChartedSpace hf n c hreg; TangentSpace (𝓡 n) y) :
    letI := levelSetChartedSpace hf n c hreg
    letI := isManifold_levelSet hf n c hreg
    g.metricInner (↑y)
        (mfderiv (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) y v)
        (mfderiv (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) y w)
      = (levelSetInducedMetric hf n c g hreg).metricInner y v w :=
  (levelSetInducedMetric_metricInner hf n c g hreg y v w).symm

section Acceleration
variable [NeZero n]

/-- **Math.** **The covariant derivative `D^{N_c}γ'/dt` exists** for every smooth
curve `γ` in the level set `N_c`, computed with the induced metric `g_{N_c}`:
its velocity field has a covariant derivative (its acceleration in `(N_c,
g_{N_c})`) at every base time.  This is `exists_hasCovDerivAlongAt_curveVelocity`
transported to `(N_c, g_{N_c})`, the intrinsic acceleration whose comparison with
the ambient one is the content of the totally-geodesic clause, item (3) of
`lem:parallel-gradient-level-sets`. -/
theorem exists_hasCovDerivAlongAt_curveVelocity_levelSet (g : RiemannianMetric I M)
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (γ : ℝ → (f ⁻¹' {c} : Set M))
    (hγ : letI := levelSetChartedSpace hf n c hreg; ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ)
    (t₀ : ℝ) :
    letI := levelSetChartedSpace hf n c hreg
    letI := isManifold_levelSet hf n c hreg
    ∃ A : EuclideanSpace ℝ (Fin n),
      HasCovDerivAlongAt (I := 𝓡 n) (levelSetInducedMetric hf n c g hreg) γ
        (curveVelocity (I := 𝓡 n) γ) t₀ A := by
  letI := levelSetChartedSpace hf n c hreg
  letI := isManifold_levelSet hf n c hreg
  haveI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
    rw [finrank_euclideanSpace_fin]; infer_instance
  exact exists_hasCovDerivAlongAt_curveVelocity (I := 𝓡 n)
    (g := levelSetInducedMetric hf n c g hreg) hγ t₀

end Acceleration

/-- **Math.** The **Riemannian product metric** `g_{N_c} ⊕ dt²` on `N_c × ℝ`:
the induced metric on the level set summed with the flat `dt²` metric on the
line (DoCarmo `DCProductMetric` of `levelSetInducedMetric` with
`DCEuclideanMetric`).  This is the domain metric of the Cheeger–Gromoll
splitting parametrization `Φ : N_c × ℝ → X`, `Φ(y,t) = θ_t(y)`; the Riemannian
form of `prop:parallel-gradient-splitting` is the pullback identity
`Φ*g = g_{N_c} ⊕ dt²`, whose ambient shadow is
`metricInner_flowVariation_of_bochner`. -/
def levelSetProductMetric (g : RiemannianMetric I M)
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    letI := levelSetChartedSpace hf n c hreg
    letI := isManifold_levelSet hf n c hreg
    RiemannianMetric ((𝓡 n).prod 𝓘(ℝ, ℝ)) ((f ⁻¹' {c} : Set M) × ℝ) :=
  letI := levelSetChartedSpace hf n c hreg
  letI := isManifold_levelSet hf n c hreg
  DCProductMetric (levelSetInducedMetric hf n c g hreg) (DCEuclideanMetric (F := ℝ))

/-- **Math.** **The product metric splits the inner product.** For level-tangent
`w, w' ∈ T_yN_c` and line components `a, b ∈ ℝ`, the Riemannian product metric
`g_{N_c} ⊕ dt²` on `N_c × ℝ` evaluates to
`⟨(w,a),(w',b)⟩_{g_{N_c}⊕dt²} = ⟨w,w'⟩_{g_{N_c}} + a·b`, the pointwise formula
underlying the domain side of the Cheeger–Gromoll splitting isometry
`Φ*g = g_{N_c} ⊕ dt²` (`prop:parallel-gradient-splitting`). -/
theorem levelSetProductMetric_metricInner (g : RiemannianMetric I M)
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (y : (f ⁻¹' {c} : Set M)) (t : ℝ)
    (w w' : letI := levelSetChartedSpace hf n c hreg; TangentSpace (𝓡 n) y)
    (a b : ℝ) :
    letI := levelSetChartedSpace hf n c hreg
    letI := isManifold_levelSet hf n c hreg
    (levelSetProductMetric hf n c g hreg).metricInner (y, t) (w, a) (w', b)
      = (levelSetInducedMetric hf n c g hreg).metricInner y w w' + a * b := by
  letI := levelSetChartedSpace hf n c hreg
  letI := isManifold_levelSet hf n c hreg
  have h := DCProductMetric_metricInner_mk (levelSetInducedMetric hf n c g hreg)
    (DCEuclideanMetric (F := ℝ)) y t w w' a b
  rw [DCEuclideanMetric_apply] at h
  rw [show (inner ℝ a b : ℝ) = a * b from by simp [inner, mul_comm]] at h
  exact h

/-- **Math.** **Ambient form of the product-metric inner product.** Combining
the split of `g_{N_c} ⊕ dt²` with the pullback identity of the induced metric,
`⟨(w,a),(w',b)⟩_{g_{N_c}⊕dt²} = ⟨dι w, dι w'⟩_g + a·b`, where `ι : N_c → M` is the
inclusion. This is the exact shape of the ambient right-hand side produced by
`metricInner_flowVariation_of_bochner`; it reduces the Riemannian form of the
splitting (`prop:parallel-gradient-splitting`, `Φ*g = g_{N_c} ⊕ dt²`) to the
differential formula `dΦ_{(y,t)}(w,a) = dθ_t(dι w) + a·∇B`. -/
theorem levelSetProductMetric_metricInner_ambient (g : RiemannianMetric I M)
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (y : (f ⁻¹' {c} : Set M)) (t : ℝ)
    (w w' : letI := levelSetChartedSpace hf n c hreg; TangentSpace (𝓡 n) y)
    (a b : ℝ) :
    letI := levelSetChartedSpace hf n c hreg
    letI := isManifold_levelSet hf n c hreg
    (levelSetProductMetric hf n c g hreg).metricInner (y, t) (w, a) (w', b)
      = g.metricInner (↑y)
          (mfderiv (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) y w)
          (mfderiv (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) y w') + a * b := by
  letI := levelSetChartedSpace hf n c hreg
  letI := isManifold_levelSet hf n c hreg
  rw [levelSetProductMetric_metricInner hf n c g hreg y t w w' a b,
    levelSetInducedMetric_metricInner hf n c g hreg y w w']

end MorganTianLib

end
