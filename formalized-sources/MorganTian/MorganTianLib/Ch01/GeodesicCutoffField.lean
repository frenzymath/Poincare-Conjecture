import MorganTianLib.Ch01.ThreePieceIndexForm

/-! # Piecewise affine cutoff fields on a minimizing geodesic -/

open Set Filter Riemannian Riemannian.Geodesic Module MeasureTheory
open scoped ContDiff Manifold Topology RealInnerProductSpace
noncomputable section
namespace MorganTianLib
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
  [CompleteSpace E] [T2Space (TangentBundle I M)]
local notation "𝔼" => EuclideanSpace ℝ (Fin (finrank ℝ E))

/-- **Math.** The index form of the affine endpoint cutoff, with a constant
plateau in between, is nonnegative. The equality case `2r = 1` has only one
corner and an empty plateau; it is included. -/
theorem cutoff_indexForm_nonneg_of_minimizing [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) {γ : ℝ → M} {a b r : ℝ}
    {e : Fin (finrank ℝ E) → ℝ → E}
    (ha : a < 0) (hb : 1 < b) (hr : 0 < r) (hr1 : 2 * r ≤ 1)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
    (hmin : Real.sqrt (speedSq (I := I) g γ 0) ≤ dist (γ 0) (γ 1)) (v : 𝔼) :
    let R := frameCurvOp (I := I) g γ e
    0 ≤ (∫ t in (0 : ℝ)..r, ⟪v, v⟫ / r ^ 2 - t ^ 2 / r ^ 2 * ⟪R t v, v⟫)
      + (∫ t in r..(1 - r), -⟪R t v, v⟫)
      + (∫ t in (1 - r)..1, ⟪v, v⟫ / r ^ 2 - (1 - t) ^ 2 / r ^ 2 * ⟪R t v, v⟫) := by
  dsimp only
  let R := frameCurvOp (I := I) g γ e
  let W₀ : ℝ → 𝔼 := fun t => (t / r) • v
  let W₁ : ℝ → 𝔼 := fun _ => v
  let W₂ : ℝ → 𝔼 := fun t => ((1 - t) / r) • v
  have hW₀ : ContDiff ℝ 3 W₀ := by dsimp [W₀]; fun_prop
  have hW₁ : ContDiff ℝ 3 W₁ := contDiff_const
  have hW₂ : ContDiff ℝ 3 W₂ := by dsimp [W₂]; fun_prop
  have hD₀ : deriv W₀ = fun _ => (1 / r) • v := by
    funext t
    exact (((hasDerivAt_id t).div_const r).smul_const v).deriv
  have hD₁ : deriv W₁ = fun _ => 0 := by funext t; exact deriv_const t v
  have hD₂ : deriv W₂ = fun _ => (-1 / r) • v := by
    funext t
    simpa using ((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).div_const r).smul_const v).deriv
  have hzero : W₀ 0 = 0 := by simp [W₀]
  have hone : W₂ 1 = 0 := by simp [W₂]
  have hmatch₀ : W₀ r = W₁ r := by simp [W₀, W₁, ne_of_gt hr]
  have hmatch₁ : W₁ (1 - r) = W₂ (1 - r) := by simp [W₁, W₂, ne_of_gt hr]
  have hI₀ : indexForm R 0 r W₀ (deriv W₀) W₀ (deriv W₀) =
      ∫ t in (0 : ℝ)..r, ⟪v, v⟫ / r ^ 2 - t ^ 2 / r ^ 2 * ⟪R t v, v⟫ := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [indexIntegrand, hD₀, W₀, map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  have hI₁ : indexForm R r (1 - r) W₁ (deriv W₁) W₁ (deriv W₁) =
      ∫ t in r..(1 - r), -⟪R t v, v⟫ := by
    apply intervalIntegral.integral_congr
    intro t _
    simp [indexIntegrand, hD₁, W₁]
  have hI₂ : indexForm R (1 - r) 1 W₂ (deriv W₂) W₂ (deriv W₂) =
      ∫ t in (1 - r)..1, ⟪v, v⟫ / r ^ 2 - (1 - t) ^ 2 / r ^ 2 * ⟪R t v, v⟫ := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [indexIntegrand, hD₂, W₂, map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [← hI₀, ← hI₁, ← hI₂]
  rcases (show r ≤ 1 - r by linarith).eq_or_lt with heq | hlt
  · have hmatch : W₀ r = W₂ r := by
      rw [hmatch₀]
      have h := hmatch₁
      rw [← heq] at h
      exact h
    rw [← heq]
    simp only [indexForm, intervalIntegral.integral_same, add_zero]
    exact indexForm_nonneg_of_minimizing (I := I) g hg ha hb hr (by linarith)
      hgeo hγc hPar horth hmin hW₀.contDiffOn hW₂ hzero hone hmatch
  · exact indexForm_threePieces_nonneg_of_minimizing (I := I) g hg ha hb hr hlt
      (by linarith) hgeo hγc hPar horth hmin hW₀.contDiffOn hW₁.contDiffOn
      hW₂.contDiffOn hzero hone hmatch₀ hmatch₁

end MorganTianLib
