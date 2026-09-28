import MorganTianLib.Ch02.FlowIsometryLocal

/-!
# Morgan–Tian Ch. 2 — the gradient flow is a global isometry

Blueprint `lem:parallel-gradient-flow`(4): under the Bochner package
(`|∇f|² ≡ c₁`, `Δf ≡ c₂`, `Ric(∇f,∇f) ≥ 0`), every time-`t` map `θ_t` of the
flow of the gradient field `(∇f)^*` is **differentiable with
metric-preserving differential** at every point:
`⟨dθ_t(v), dθ_t(w)⟩_{θ_t(x)} = ⟨v, w⟩_x`. Together with the homeomorphism
property (`smoothVectorFieldFlowHomeomorph`, FlowContinuity.lean) this is the
isometry claim `θ_t^* g = g` of the blueprint.

The global statement follows from the local isometry step
(`exists_flowIsometryBoxAt`) by the group law: the compact orbit arc
`{θ_u(x) : |u| ≤ |t|}` is covered by finitely many isometry flow boxes, `t`
is split into `n` equal steps shorter than the uniform box time, and
`θ_t = θ_{t/n} ∘ ⋯ ∘ θ_{t/n}` composes the local metric-preserving
differentials along the orbit (chain rule for `mfderiv`).

Main declarations:

* `metricPreservingAt_smoothVectorFieldFlow_nsmul_of_bochner` — the
  induction: `n` short steps along the orbit compose.
* `metricPreserving_smoothVectorFieldFlow_of_bochner` — blueprint
  `lem:parallel-gradient-flow`(4): `θ_t` is differentiable at every point
  with inner-product-preserving differential.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4
(blueprint `lem:parallel-gradient-flow`).
-/

open Set Filter Function Metric Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **The step induction**: if every point of a set `K` admits the
metric-preserving property for all times `|s'| ≤ δ`, then the `n`-fold
composite `θ_{n·s}` (with `|s| ≤ δ`) is differentiable with
metric-preserving differential at any `x` whose orbit points
`θ_{j·s}(x)`, `j < n`, all lie in `K`. Blueprint
`lem:parallel-gradient-flow`(4), group-law induction. -/
theorem metricPreservingAt_smoothVectorFieldFlow_nsmul_of_bochner
    (g : RiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    {K : Set M} {δ : ℝ}
    (hstep : ∀ y ∈ K, ∀ s' : ℝ, |s'| ≤ δ →
      MDifferentiableAt I I
        (smoothVectorFieldFlow (gradientField g f hf) hex s') y ∧
      ∀ v w : TangentSpace I y,
        g.metricInner (smoothVectorFieldFlow (gradientField g f hf) hex s' y)
          (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex s') y v)
          (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex s') y w)
        = g.metricInner y v w)
    {s : ℝ} (hs : |s| ≤ δ) :
    ∀ (n : ℕ) (x : M),
      (∀ j : ℕ, j < n →
        smoothVectorFieldFlow (gradientField g f hf) hex (j * s) x ∈ K) →
      MDifferentiableAt I I
        (smoothVectorFieldFlow (gradientField g f hf) hex (n * s)) x ∧
      ∀ v w : TangentSpace I x,
        g.metricInner
          (smoothVectorFieldFlow (gradientField g f hf) hex (n * s) x)
          (mfderiv I I
            (smoothVectorFieldFlow (gradientField g f hf) hex (n * s)) x v)
          (mfderiv I I
            (smoothVectorFieldFlow (gradientField g f hf) hex (n * s)) x w)
        = g.metricInner x v w := by
  intro n
  induction n with
  | zero =>
    intro x _
    have hid : smoothVectorFieldFlow (gradientField g f hf) hex ((0:ℕ) * s)
        = (id : M → M) := by
      funext x'
      rw [show ((0:ℕ) : ℝ) * s = 0 by push_cast; ring]
      exact smoothVectorFieldFlow_zero _ hex x'
    rw [hid]
    refine ⟨mdifferentiableAt_id, fun v w => ?_⟩
    rw [mfderiv_id]
    rfl
  | succ n ih =>
    intro x horbit
    -- the group-law decomposition of the `(n+1)`-st step
    have hfun : smoothVectorFieldFlow (gradientField g f hf) hex
          (((n:ℕ)+1 : ℕ) * s)
        = fun x' => smoothVectorFieldFlow (gradientField g f hf) hex s
            (smoothVectorFieldFlow (gradientField g f hf) hex ((n:ℝ) * s) x') := by
      funext x'
      rw [show ((((n:ℕ)+1 : ℕ)) : ℝ) * s = s + (n:ℝ) * s by push_cast; ring]
      exact smoothVectorFieldFlow_add _ hex s ((n:ℝ) * s) x'
    have hihyp : ∀ j : ℕ, j < n →
        smoothVectorFieldFlow (gradientField g f hf) hex (j * s) x ∈ K :=
      fun j hj => horbit j (Nat.lt_succ_of_lt hj)
    obtain ⟨ihd, ihm⟩ := ih x hihyp
    have hyK : smoothVectorFieldFlow (gradientField g f hf) hex ((n:ℝ) * s) x ∈ K := by
      have := horbit n (Nat.lt_succ_self n)
      simpa using this
    obtain ⟨hsd, hsm⟩ := hstep _ hyK s hs
    -- differentiability of the composite
    have hmd : MDifferentiableAt I I
        (fun x' => smoothVectorFieldFlow (gradientField g f hf) hex s
          (smoothVectorFieldFlow (gradientField g f hf) hex ((n:ℝ) * s) x')) x :=
      hsd.comp x ihd
    constructor
    · rw [hfun]
      exact hmd
    · intro v w
      rw [hfun]
      have hcomp : mfderiv I I
          (fun x' => smoothVectorFieldFlow (gradientField g f hf) hex s
            (smoothVectorFieldFlow (gradientField g f hf) hex ((n:ℝ) * s) x')) x
          = (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex s)
              (smoothVectorFieldFlow (gradientField g f hf) hex ((n:ℝ) * s) x)).comp
            (mfderiv I I
              (smoothVectorFieldFlow (gradientField g f hf) hex ((n:ℝ) * s)) x) :=
        mfderiv_comp x hsd ihd
      rw [hcomp]
      show g.metricInner _
          (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex s) _
            (mfderiv I I
              (smoothVectorFieldFlow (gradientField g f hf) hex ((n:ℝ) * s)) x v))
          (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex s) _
            (mfderiv I I
              (smoothVectorFieldFlow (gradientField g f hf) hex ((n:ℝ) * s)) x w))
        = g.metricInner x v w
      rw [hsm, ihm]

/-- **Math.** **The gradient flow preserves the metric** (blueprint
`lem:parallel-gradient-flow`(4)): under the Bochner package, for every
`t ∈ ℝ` the flow map `θ_t` of the gradient field is differentiable at every
point `x`, and its differential preserves the Riemannian inner product:
`⟨dθ_t(v), dθ_t(w)⟩_{θ_t(x)} = ⟨v, w⟩_x`. Together with
`smoothVectorFieldFlowHomeomorph` this makes each `θ_t` an isometry
`θ_t^* g = g` of `(X, g)`. -/
theorem metricPreserving_smoothVectorFieldFlow_of_bochner
    (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (t : ℝ) (x : M) :
    MDifferentiableAt I I
      (smoothVectorFieldFlow (gradientField g f hf) hex t) x ∧
    ∀ v w : TangentSpace I x,
      g.metricInner (smoothVectorFieldFlow (gradientField g f hf) hex t x)
        (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex t) x v)
        (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex t) x w)
      = g.metricInner x v w := by
  classical
  -- the compact orbit arc through `x`
  set K : Set M := (fun u => smoothVectorFieldFlow (gradientField g f hf) hex u x)
    '' Icc (-|t|) |t| with hK_def
  have hKcompact : IsCompact K :=
    isCompact_Icc.image (continuous_smoothVectorFieldFlow_apply _ hex x)
  -- an isometry flow box around every point of the arc
  choose! δ V hδ hVopen hVmem hVstep using fun y : M =>
    exists_flowIsometryBoxAt g hLC hf hgrad hharm hric hex y
  obtain ⟨T', hT'K, hKT'⟩ := hKcompact.elim_nhds_subcover V
    fun y _ => (hVopen y).mem_nhds (hVmem y)
  have hxK : x ∈ K := ⟨0, ⟨neg_nonpos.mpr (abs_nonneg t), abs_nonneg t⟩,
    smoothVectorFieldFlow_zero _ hex x⟩
  have hT'ne : T'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty T' with hT0 | hT0
    · exfalso
      subst hT0
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty,
        subset_empty_iff] at hKT'
      rw [hKT'] at hxK
      exact hxK
    · exact hT0
  -- the uniform box time over the finite subcover
  set δ₀ : ℝ := T'.inf' hT'ne δ with hδ₀_def
  have hδ₀ : 0 < δ₀ := (Finset.lt_inf'_iff _).mpr fun y _ => hδ y
  have hδ₀le : ∀ y ∈ T', δ₀ ≤ δ y := fun y hy => Finset.inf'_le _ hy
  -- the uniform step property on the arc
  have hstep : ∀ y ∈ K, ∀ s' : ℝ, |s'| ≤ δ₀ →
      MDifferentiableAt I I
        (smoothVectorFieldFlow (gradientField g f hf) hex s') y ∧
      ∀ v w : TangentSpace I y,
        g.metricInner (smoothVectorFieldFlow (gradientField g f hf) hex s' y)
          (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex s') y v)
          (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex s') y w)
        = g.metricInner y v w := by
    intro y hy s' hs'
    obtain ⟨z, hzT', hyz⟩ := mem_iUnion₂.mp (hKT' hy)
    obtain ⟨h1, h2⟩ := hVstep z y hyz s' (le_trans hs' (hδ₀le z hzT'))
    exact ⟨h1.mdifferentiableAt one_ne_zero, h2⟩
  -- choose the number of steps
  obtain ⟨n, hn⟩ := exists_nat_gt (|t| / δ₀)
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      rw [h0] at hn
      exact absurd hn (not_lt.mpr (by push_cast; positivity))
    · exact hpos
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
  set s : ℝ := t / n with hs_def
  have habs_t : |t| < (n:ℝ) * δ₀ := (div_lt_iff₀ hδ₀).mp hn
  have hs : |s| ≤ δ₀ := by
    rw [hs_def, abs_div, abs_of_nonneg hnR.le, div_le_iff₀ hnR]
    linarith
  -- the orbit points stay on the compact arc
  have horbit : ∀ j : ℕ, j < n →
      smoothVectorFieldFlow (gradientField g f hf) hex (j * s) x ∈ K := by
    intro j hj
    refine ⟨j * s, ?_, rfl⟩
    have hjn : (j:ℝ) ≤ (n:ℝ) := by exact_mod_cast hj.le
    have hjs : |(j:ℝ) * s| ≤ |t| := by
      rw [abs_mul, hs_def, abs_div, abs_of_nonneg hnR.le,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (j:ℝ))]
      have h1 : (j:ℝ) * (|t| / n) ≤ (n:ℝ) * (|t| / n) :=
        mul_le_mul_of_nonneg_right hjn (by positivity)
      have h2 : (n:ℝ) * (|t| / n) = |t| := by field_simp
      linarith
    exact ⟨neg_le_of_abs_le hjs, le_of_abs_le hjs⟩
  -- split `t` into `n` equal short steps and compose
  have ht_eq : (n:ℝ) * s = t := by
    rw [hs_def]
    field_simp
  have hmain := metricPreservingAt_smoothVectorFieldFlow_nsmul_of_bochner
    g hf hex hstep hs n x horbit
  rwa [ht_eq] at hmain

end MorganTianLib

end
