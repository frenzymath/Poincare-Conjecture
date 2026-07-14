import MorganTianLib.Ch01.JacobiManifold
import MorganTianLib.Ch02.GradientFlow
import OpenGALib.Riemannian.Geodesic.HopfRinow.MetricBridge

/-!
# Morgan–Tian Ch. 2 — a function with unit gradient is `1`-Lipschitz

Blueprint `prop:parallel-gradient-splitting` (Step 4) and
`lem:busemann-gradient-norm-one` infrastructure: a smooth function `f` whose
gradient satisfies `|∇f| ≤ 1` pointwise decreases along `C¹` paths no faster
than arclength, hence `|f x − f y| ≤ d(x, y)` for the Riemannian distance.
This is the "vertical" lower bound of the metric splitting: since
`f (θ_t x) = f x + t` along the gradient flow, the `1`-Lipschitz bound forces
`d(x, θ_t x) ≥ |t|`, which combines with the geodesic upper bound to make
every flow line a **minimizing line** (`FlowLineMinimizing.lean`).

The chain is elementary:

* `abs_metricInner_le_sqrt_mul_sqrt` — the **Cauchy–Schwarz inequality** for
  the Riemannian fibre inner product in square-root form, from the squared
  form `metricInner_sq_le` (`MorganTianLib.Ch01.JacobiManifold`).
* `ofReal_abs_sub_le_pathELength` — the **fundamental theorem of calculus
  along a path**: if `|df_q(v)| ≤ √(g_q(v,v))` for all `q, v`, then for any
  path `γ` that is `C¹` on `[a, b]`,
  `|f (γ b) − f (γ a)| = |∫ (f ∘ γ)'| ≤ ∫ |df(γ')| ≤ ∫ |γ'|ₑ`, the
  `g`-length of `γ`. Stated for an arbitrary fibre `ENorm` instance computing
  `‖v‖ₑ = √(g(v,v))`, as in `FlowMetricIsometry.lean`.
* `ofReal_abs_sub_le_edist_of_bochner` / `abs_sub_le_dist_of_bochner` — the
  `1`-Lipschitz bound `|f x − f y| ≤ d(x, y)` for a Bochner function with
  `|∇f|² ≡ 1`, by taking the infimum over `C¹` paths.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4
(proof of Lemma 2.14 / the splitting theorem).
-/

open Set Bundle Filter Function Metric Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

section CauchySchwarz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** **Cauchy–Schwarz for the Riemannian metric** in square-root
form: `|g_x(v, w)| ≤ √(g_x(v,v)) · √(g_x(w,w))`, from the squared form
`metricInner_sq_le`. -/
theorem abs_metricInner_le_sqrt_mul_sqrt (g : RiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    |g.metricInner x v w|
      ≤ Real.sqrt (g.metricInner x v v) * Real.sqrt (g.metricInner x w w) :=
  calc |g.metricInner x v w|
      = Real.sqrt (g.metricInner x v w ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (g.metricInner x v v * g.metricInner x w w) :=
        Real.sqrt_le_sqrt (metricInner_sq_le (I := I) g x v w)
    _ = Real.sqrt (g.metricInner x v v) * Real.sqrt (g.metricInner x w w) :=
        Real.sqrt_mul (metricInner_self_nonneg (I := I) g x v) _

end CauchySchwarz

section PathBound

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The differential `df_q(v)` of a real-valued function `f` at `q`
in the direction `v`, as a real number. (`TangentSpace 𝓘(ℝ, ℝ) y` is
definitionally `ℝ`, but instance synthesis does not unfold it, so statements
about `|df_q(v)|` need this retyped form.) -/
def mfderivReal (f : M → ℝ) (q : M) (v : TangentSpace I q) : ℝ :=
  mfderiv I 𝓘(ℝ, ℝ) f q v

@[simp] theorem mfderivReal_def (f : M → ℝ) (q : M) (v : TangentSpace I q) :
    mfderivReal (I := I) f q v = mfderiv I 𝓘(ℝ, ℝ) f q v := rfl

/-- **Math.** **The fundamental theorem of calculus along a path**: if a
smooth `f : M → ℝ` has differential bounded by the metric,
`|df_q(v)| ≤ √(g_q(v,v))` for all `q, v`, then along any path `γ` that is
`C¹` on `[a, b]` the variation of `f` is bounded by the `g`-length:
`|f (γ b) − f (γ a)| ≤ pathELength γ a b`. Stated for an arbitrary fibre
`ENorm` instance computing `‖v‖ₑ = √(g(v,v))` (hypothesis `henorm`).
Blueprint `prop:parallel-gradient-splitting` (Step 4). -/
theorem ofReal_abs_sub_le_pathELength
    [∀ x : M, ENorm (TangentSpace I x)]
    (g : RiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hdf : ∀ (q : M) (v : TangentSpace I q),
      |mfderivReal (I := I) f q v| ≤ Real.sqrt (g.metricInner q v v))
    (henorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.metricInner x v v)))
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) :
    ENNReal.ofReal |f (γ b) - f (γ a)| ≤ Manifold.pathELength I γ a b := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  -- `φ = f ∘ γ` is `C¹` on `[a, b]`, with continuous `derivWithin`.
  have hφm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (f ∘ γ) (Icc a b) :=
    (hf.of_le (by norm_num)).comp_contMDiffOn hγ
  have hφ : ContDiffOn ℝ 1 (f ∘ γ) (Icc a b) := by
    rwa [contMDiffOn_iff_contDiffOn] at hφm
  have hUD : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hlt
  have hφdcont : ContinuousOn (derivWithin (f ∘ γ) (Icc a b)) (Icc a b) :=
    hφ.continuousOn_derivWithin hUD le_rfl
  -- On the interior, `derivWithin φ` is a genuine derivative.
  have hderiv : ∀ t ∈ Ioo a b,
      HasDerivAt (f ∘ γ) (derivWithin (f ∘ γ) (Icc a b) t) t := by
    intro t ht
    have hmem : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hdiff : DifferentiableAt ℝ (f ∘ γ) t :=
      ((hφ.differentiableOn one_ne_zero) t
        (Ioo_subset_Icc_self ht)).differentiableAt hmem
    rw [derivWithin_of_mem_nhds hmem]
    exact hdiff.hasDerivAt
  have hint : IntervalIntegrable (derivWithin (f ∘ γ) (Icc a b))
      MeasureTheory.volume a b :=
    (hφdcont.mono (by rw [uIcc_of_le hab])).intervalIntegrable
  -- FTC: the variation of `f` is the integral of `derivWithin φ`.
  have hFTC : ∫ t in a..b, derivWithin (f ∘ γ) (Icc a b) t
      = f (γ b) - f (γ a) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hφ.continuousOn
      hderiv hint
  have habs : |f (γ b) - f (γ a)|
      ≤ ∫ t in a..b, |derivWithin (f ∘ γ) (Icc a b) t| := by
    rw [← hFTC]
    exact intervalIntegral.abs_integral_le_integral_abs hab
  -- Pass to the `ℝ≥0∞`-valued integral and compare with the length integrand.
  have hlint : ENNReal.ofReal
      (∫ t in a..b, |derivWithin (f ∘ γ) (Icc a b) t|)
      = ∫⁻ t in Ioc a b, ENNReal.ofReal
          |derivWithin (f ∘ γ) (Icc a b) t| := by
    rw [intervalIntegral.integral_of_le hab]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint.abs.1
      (Filter.Eventually.of_forall fun t => abs_nonneg _)
  calc ENNReal.ofReal |f (γ b) - f (γ a)|
      ≤ ENNReal.ofReal (∫ t in a..b, |derivWithin (f ∘ γ) (Icc a b) t|) :=
        ENNReal.ofReal_le_ofReal habs
    _ = ∫⁻ t in Ioc a b, ENNReal.ofReal
          |derivWithin (f ∘ γ) (Icc a b) t| := hlint
    _ = ∫⁻ t in Ioo a b, ENNReal.ofReal
          |derivWithin (f ∘ γ) (Icc a b) t| := by
        rw [MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    _ ≤ ∫⁻ t in Ioo a b, ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ := ?_
    _ = Manifold.pathELength I γ a b :=
        (Manifold.pathELength_eq_lintegral_mfderiv_Ioo).symm
  -- The pointwise bound on the interior: chain rule plus `hdf`.
  refine MeasureTheory.setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
  have hmem : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hγt : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    ((hγ t (Ioo_subset_Icc_self ht)).contMDiffAt hmem).mdifferentiableAt
      one_ne_zero
  have hft : MDifferentiableAt I 𝓘(ℝ, ℝ) f (γ t) :=
    (hf (γ t)).mdifferentiableAt (by norm_num)
  have hphi : derivWithin (f ∘ γ) (Icc a b) t
      = mfderiv I 𝓘(ℝ, ℝ) f (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := by
    rw [derivWithin_of_mem_nhds hmem]
    have hcomp : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ γ) t
        = (mfderiv I 𝓘(ℝ, ℝ) f (γ t)).comp (mfderiv 𝓘(ℝ, ℝ) I γ t) :=
      mfderiv_comp t hft hγt
    have hdd : deriv (f ∘ γ) t = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ γ) t 1 := by
      rw [mfderiv_eq_fderiv]
      exact (fderiv_apply_one_eq_deriv).symm
    rw [hdd, hcomp]
    rfl
  rw [hphi, henorm (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)]
  exact ENNReal.ofReal_le_ofReal (hdf (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1))

end PathBound

section Lipschitz

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **A function with unit gradient is `1`-Lipschitz for the
Riemannian distance** (edist form): if `|∇f|² ≡ 1` and the ambient distance
of `M` is the Riemannian distance of `g`, then
`|f x − f y| ≤ d(x, y)`. Any `C¹` path from `x` to `y` witnesses the bound by
the fundamental theorem of calculus and Cauchy–Schwarz; take the infimum.
Blueprint `prop:parallel-gradient-splitting` (Step 4). -/
theorem ofReal_abs_sub_le_edist_of_bochner
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (x y : M) :
    ENNReal.ofReal |f x - f y| ≤ edist x y := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M := hg
  letI instE : ∀ x : M, ENorm (TangentSpace I x) := fun x =>
    SeminormedAddGroup.toContinuousENorm.toENorm
  have hout : ∀ p q : M, edist p q = Manifold.riemannianEDist I p q :=
    fun p q => IsRiemannianManifold.out p q
  rw [hout x y]
  -- differential bound from `|∇f| ≡ 1` and Cauchy–Schwarz
  have hdf : ∀ (q : M) (v : TangentSpace I q),
      |mfderivReal (I := I) f q v| ≤ Real.sqrt (g.metricInner q v v) := by
    intro q v
    have hRiesz : mfderivReal (I := I) f q v
        = g.metricInner q (gradientAt g f q) v :=
      (metricInner_gradientAt g f q v).symm
    have hCS := abs_metricInner_le_sqrt_mul_sqrt g q (gradientAt g f q) v
    have hunit : g.metricInner q (gradientAt g f q) (gradientAt g f q) = 1 :=
      hgrad q
    rw [hunit, Real.sqrt_one, one_mul] at hCS
    rw [hRiesz]
    exact hCS
  have henorm : ∀ (p : M) (v : TangentSpace I p),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.metricInner p v v)) :=
    fun p v => Riemannian.enorm_tangent_eq_sqrt_metricInner (I := I) g p v
  apply le_of_forall_gt fun r hr => ?_
  obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hr
  have hbound := ofReal_abs_sub_le_pathELength (I := I) g hf hdf henorm
    zero_le_one hγsmooth
  rw [hγ0, hγ1] at hbound
  calc ENNReal.ofReal |f x - f y|
      = ENNReal.ofReal |f y - f x| := by rw [abs_sub_comm]
    _ ≤ Manifold.pathELength I γ 0 1 := hbound
    _ < r := hγlen

/-- **Math.** **A function with unit gradient is `1`-Lipschitz for the
Riemannian distance** (dist form): `|f x − f y| ≤ dist x y`.
Blueprint `prop:parallel-gradient-splitting` (Step 4). -/
theorem abs_sub_le_dist_of_bochner
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (x y : M) :
    |f x - f y| ≤ dist x y := by
  have h := ofReal_abs_sub_le_edist_of_bochner g hg hf hgrad x y
  rw [edist_dist] at h
  exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp h

end Lipschitz

end MorganTianLib

end
