import MorganTianLib.Ch02.CurveAcceleration
import MorganTianLib.Ch02.LevelSetGeodesic

/-!
# Morgan–Tian Ch. 2 — tangential acceleration on a Bochner level set

For a smooth curve `γ` whose image lies in a level set `N_c = f⁻¹(c)` of a
Bochner function `f` (`Hess f ≡ 0`, `|∇f| ≡ 1`, `Ric ≥ 0`), the acceleration
`Dγ'/dt` is **orthogonal to the gradient** `V = (∇f)^*`, hence tangent to
`N_c = ker(dB) = V^⊥`.  This is `eq:tangential-acceleration` in the proof of the
totally-geodesic clause, item (3) of `lem:parallel-gradient-level-sets`.

The argument differentiates the pairing `⟨V∘γ, γ'⟩ = (f∘γ)' ≡ 0` (constant,
since `γ ⊂ N_c`).  By the metric product rule
(`HasCovDerivAlongAt.hasDerivAt_metricInner`) its derivative is
`⟨D(V∘γ)/dt, γ'⟩ + ⟨V∘γ, Dγ'/dt⟩`; the first term vanishes because `V∘γ` is
parallel (`isParallelAlong_gradientField_comp_of_bochner`), leaving exactly
`⟨V∘γ, Dγ'/dt⟩ = 0`.  The acceleration `Dγ'/dt` itself is furnished by
`exists_hasCovDerivAlongAt_curveVelocity`.
-/

open Set Filter Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

/-- **Math.** The pointwise pairing of the Bochner gradient with the velocity of
a smooth curve lying in a level set vanishes: `⟨V(γ s), γ'(s)⟩ = (f∘γ)'(s) = 0`,
because `f∘γ ≡ c` is constant. -/
theorem metricInner_gradientField_curveVelocity_eq_zero_of_level
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {c : ℝ}
    (hlevel : ∀ t, f (γ t) = c) (s : ℝ) :
    g.metricInner (γ s) (gradientField g f hf (γ s))
      (curveVelocity (I := I) γ s) = 0 := by
  obtain ⟨v, hv⟩ : ∃ v : E, HasDerivAt (chartLocalCurve (I := I) γ s) v s :=
    ⟨_, ((contDiffAt_chartLocalCurve hγ s).differentiableAt (by norm_cast)).hasDerivAt⟩
  have hveq : curveVelocity (I := I) γ s = (v : TangentSpace I (γ s)) :=
    curveVelocity_eq_of_hasDerivAt (I := I) hv
  have hchain : HasDerivAt (fun u => f (γ u))
      (mfderiv I 𝓘(ℝ, ℝ) f (γ s) (v : TangentSpace I (γ s))) s :=
    hasDerivAt_comp_chartLocalCurve (I := I) hf hγ.continuous.continuousAt hv
  have hconst : HasDerivAt (fun u => f (γ u)) 0 s := by
    have hfun : (fun u => f (γ u)) = fun _ => c := funext hlevel
    rw [hfun]; exact hasDerivAt_const s c
  have hmf : mfderiv I 𝓘(ℝ, ℝ) f (γ s) (v : TangentSpace I (γ s)) = 0 :=
    hchain.unique hconst
  rw [hveq, gradientField_apply, metricInner_gradientAt]
  exact hmf

/-- **Math.** **Tangential acceleration** (`eq:tangential-acceleration`): for a
smooth curve `γ` whose image lies in a Bochner level set `N_c = f⁻¹(c)`, its
acceleration `Dγ'/dt(t₀) = A` is orthogonal to the gradient `V = (∇f)^*`, i.e.
`A ∈ ker(dB) = T_{γ t₀}N_c`.  The infrastructural heart of the totally-geodesic
clause, item (3) of `lem:parallel-gradient-level-sets`. -/
theorem metricInner_gradientField_covDerivVelocity_eq_zero_of_level
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {c : ℝ} (hlevel : ∀ t, f (γ t) = c)
    (t₀ : ℝ) {A : E}
    (hA : HasCovDerivAlongAt (I := I) g γ (curveVelocity (I := I) γ) t₀ A) :
    g.metricInner (γ t₀) (gradientField g f hf (γ t₀)) A = 0 := by
  -- chart-membership and velocity data feeding the parallel-gradient lemma
  have hmem : ∀ s, ∀ᶠ u in 𝓝 s, γ u ∈ (chartAt H (γ s)).source := fun s =>
    eventually_mem_chartAt_source hγ.continuous.continuousAt
  have hvel : ∀ s, ∃ v : E, HasDerivAt (chartLocalCurve (I := I) γ s) v s := fun s =>
    ⟨_, ((contDiffAt_chartLocalCurve hγ s).differentiableAt (by norm_cast)).hasDerivAt⟩
  -- `V∘γ` is parallel along `γ`
  have hpar : IsParallelAlong (I := I) g γ (fun t => gradientField g f hf (γ t)) :=
    isParallelAlong_gradientField_comp_of_bochner (I := I) g hLC hf hgrad hharm hric hmem hvel
  -- product rule: `d/dt ⟨V∘γ, γ'⟩ = ⟨0, γ'⟩ + ⟨V∘γ, A⟩`
  have hprod := (hpar t₀).hasDerivAt_metricInner hA
  have hz : g.metricInner (γ t₀) ((0 : E) : TangentSpace I (γ t₀))
      (curveVelocity (I := I) γ t₀) = 0 :=
    g.metricInner_zero_left (γ t₀) (curveVelocity (I := I) γ t₀)
  rw [hz, zero_add] at hprod
  -- the pairing `⟨V∘γ, γ'⟩` is identically zero
  have hzero : (fun t => g.metricInner (γ t) (gradientField g f hf (γ t))
      (curveVelocity (I := I) γ t)) = fun _ => (0 : ℝ) :=
    funext fun t => metricInner_gradientField_curveVelocity_eq_zero_of_level
      (I := I) g hf hγ hlevel t
  have hF0 : HasDerivAt (fun t => g.metricInner (γ t) (gradientField g f hf (γ t))
      (curveVelocity (I := I) γ t)) 0 t₀ := by
    rw [hzero]; exact hasDerivAt_const t₀ 0
  exact hprod.unique hF0

end MorganTianLib

end
