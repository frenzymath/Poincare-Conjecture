import PoincareLib.Ch02.FlowIsometry

/-!
# Morgan–Tian Ch. 2 — each time-`t` gradient flow map is `C¹`

Blueprint `lem:parallel-gradient-flow`(2), spatial regularity: under the
Bochner package (`|∇f|² ≡ c₁`, `Δf ≡ c₂`, `Ric(∇f,∇f) ≥ 0`), every time-`t`
map `θ_t` of the flow of the gradient field `(∇f)^*` is **`C¹` at every
point**. This upgrades the everywhere-differentiability delivered by
`metricPreserving_smoothVectorFieldFlow_of_bochner` to genuine continuous
differentiability, the regularity needed to push `C¹` paths through `θ_t`
(and hence to promote the metric-preserving differential to a genuine
metric-space isometry, `FlowMetricIsometry.lean`).

The global statement follows from the local `C¹` flow-box step
(`exists_flowIsometryBoxAt`, whose boxes are `C¹` since the chart flow has
strict derivatives at every point of the flow ball) by the group law: the
compact orbit arc `{θ_u(x) : |u| ≤ |t|}` is covered by finitely many boxes,
`t` is split into `n` equal steps shorter than the uniform box time, and
`θ_t = θ_{t/n} ∘ ⋯ ∘ θ_{t/n}` composes the local `C¹` maps along the orbit.

Main declarations:

* `contMDiffAt_smoothVectorFieldFlow_nsmul_of_bochner` — the induction:
  `n` short `C¹` steps along the orbit compose.
* `contMDiffAt_smoothVectorFieldFlow_of_bochner` — `θ_t` is `C¹` at every
  point.
* `contMDiff_smoothVectorFieldFlow_of_bochner` — `θ_t` is `C¹` as a map
  `M → M`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4
(blueprint `lem:parallel-gradient-flow`).
-/

open Set Filter Function Metric Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **The step induction for `C¹` regularity**: if every point of a
set `K` admits the `C¹` property for all times `|s'| ≤ δ`, then the `n`-fold
composite `θ_{n·s}` (with `|s| ≤ δ`) is `C¹` at any `x` whose orbit points
`θ_{j·s}(x)`, `j < n`, all lie in `K`. Blueprint
`lem:parallel-gradient-flow`(2), group-law induction. -/
theorem contMDiffAt_smoothVectorFieldFlow_nsmul_of_bochner
    (g : RiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    {K : Set M} {δ : ℝ}
    (hstep : ∀ y ∈ K, ∀ s' : ℝ, |s'| ≤ δ →
      ContMDiffAt I I 1
        (smoothVectorFieldFlow (gradientField g f hf) hex s') y)
    {s : ℝ} (hs : |s| ≤ δ) :
    ∀ (n : ℕ) (x : M),
      (∀ j : ℕ, j < n →
        smoothVectorFieldFlow (gradientField g f hf) hex (j * s) x ∈ K) →
      ContMDiffAt I I 1
        (smoothVectorFieldFlow (gradientField g f hf) hex (n * s)) x := by
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
    exact contMDiffAt_id
  | succ n ih =>
    intro x horbit
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
    have ihx := ih x hihyp
    have hyK : smoothVectorFieldFlow (gradientField g f hf) hex ((n:ℝ) * s) x
        ∈ K := by
      have := horbit n (Nat.lt_succ_self n)
      simpa using this
    have hsx := hstep _ hyK s hs
    rw [hfun]
    exact hsx.comp x ihx

/-- **Math.** **Each time-`t` gradient flow map is `C¹`** (blueprint
`lem:parallel-gradient-flow`(2), spatial regularity): under the Bochner
package, for every `t ∈ ℝ` the flow map `θ_t` of the gradient field is `C¹`
at every point `x`. The compact orbit arc through `x` is covered by finitely
many `C¹` flow boxes and `t` is split into short steps. -/
theorem contMDiffAt_smoothVectorFieldFlow_of_bochner
    (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (t : ℝ) (x : M) :
    ContMDiffAt I I 1
      (smoothVectorFieldFlow (gradientField g f hf) hex t) x := by
  classical
  -- the compact orbit arc through `x`
  set K : Set M := (fun u => smoothVectorFieldFlow (gradientField g f hf) hex u x)
    '' Icc (-|t|) |t| with hK_def
  have hKcompact : IsCompact K :=
    isCompact_Icc.image (continuous_smoothVectorFieldFlow_apply _ hex x)
  -- a `C¹` isometry flow box around every point of the arc
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
  -- the uniform `C¹` step property on the arc
  have hstep : ∀ y ∈ K, ∀ s' : ℝ, |s'| ≤ δ₀ →
      ContMDiffAt I I 1
        (smoothVectorFieldFlow (gradientField g f hf) hex s') y := by
    intro y hy s' hs'
    obtain ⟨z, hzT', hyz⟩ := mem_iUnion₂.mp (hKT' hy)
    exact (hVstep z y hyz s' (le_trans hs' (hδ₀le z hzT'))).1
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
  have hmain := contMDiffAt_smoothVectorFieldFlow_nsmul_of_bochner
    g hf hex hstep hs n x horbit
  rwa [ht_eq] at hmain

/-- **Math.** **Each time-`t` gradient flow map is `C¹` as a map `M → M`**
(blueprint `lem:parallel-gradient-flow`(2), spatial regularity, global
form). -/
theorem contMDiff_smoothVectorFieldFlow_of_bochner
    (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (t : ℝ) :
    ContMDiff I I 1 (smoothVectorFieldFlow (gradientField g f hf) hex t) :=
  fun x => (contMDiffAt_smoothVectorFieldFlow_of_bochner g hLC hf hgrad hharm
    hric hex t x).contMDiffWithinAt

end PoincareLib

end
