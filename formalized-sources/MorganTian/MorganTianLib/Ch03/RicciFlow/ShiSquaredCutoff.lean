import MorganTianLib.Ch03.RicciFlow.ShiCutoffBounds
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Tactic.Linarith

/-!
# A squared Euclidean cutoff for Shi localization

Squaring the standard smooth bump preserves its plateau and support while
turning a global first-derivative bound for the bump into the quotient bound
`‖d eta‖ ^ 2 / eta <= G` used at a weighted maximum.
-/

open scoped ContDiff

noncomputable section

namespace MorganTianLib

/-- The squared Euclidean Shi cutoff.  The square is the standard device that
makes the gradient-to-value quotient uniformly bounded near the edge of the
support. -/
def shiEuclideanSquaredCutoff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r : ℝ) (hr : 0 < r) : E → ℝ :=
  (ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr)) ^ 2

theorem shiEuclideanSquaredCutoff_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (shiEuclideanSquaredCutoff (E := E) r hr) := by
  exact (shiEuclideanCutoff_contDiff (E := E) hr).pow 2

theorem shiEuclideanSquaredCutoff_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r : ℝ) (hr : 0 < r) (x : E) :
    0 ≤ shiEuclideanSquaredCutoff r hr x := by
  exact sq_nonneg _

theorem shiEuclideanSquaredCutoff_le_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r : ℝ) (hr : 0 < r) (x : E) :
    shiEuclideanSquaredCutoff r hr x ≤ 1 := by
  have hnonneg := shiEuclideanCutoff_nonneg r hr x
  have hle := shiEuclideanCutoff_le_one r hr x
  dsimp [shiEuclideanSquaredCutoff]
  nlinarith

theorem shiEuclideanSquaredCutoff_eq_one_of_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r : ℝ} (hr : 0 < r) {x : E}
    (hx : x ∈ Metric.closedBall (0 : E) (r / 4)) :
    shiEuclideanSquaredCutoff r hr x = 1 := by
  change (ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr) x) ^ 2 = 1
  rw [shiEuclideanCutoff_eq_one_of_mem hr hx]
  norm_num

theorem shiEuclideanSquaredCutoff_eq_zero_of_not_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r : ℝ} (hr : 0 < r) {x : E}
    (hx : x ∉ Metric.ball (0 : E) (r / 2)) :
    shiEuclideanSquaredCutoff r hr x = 0 := by
  change (ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr) x) ^ 2 = 0
  rw [shiEuclideanCutoff_eq_zero_of_not_mem hr hx]
  norm_num

theorem shiEuclideanSquaredCutoff_hasCompactSupport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (shiEuclideanSquaredCutoff (E := E) r hr) := by
  rw [HasCompactSupport]
  have hsupp : Function.support (shiEuclideanSquaredCutoff (E := E) r hr) =
      Function.support
        (ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr)) := by
    ext x
    simp [Function.mem_support, shiEuclideanSquaredCutoff]
  have hts : tsupport (shiEuclideanSquaredCutoff (E := E) r hr) =
      tsupport (ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr)) := by
    simp only [tsupport, hsupp]
  rw [hts]
  exact shiEuclideanCutoff_hasCompactSupport (E := E) hr

/-- A global quotient bound for the squared Euclidean cutoff.  The constant is
explicit in terms of any global first-derivative bound for the unsquared bump. -/
theorem shiEuclideanSquaredCutoff_gradient_ratio_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r C₁ : ℝ} (hr : 0 < r) (hC₁ : 0 ≤ C₁)
    (hderiv : ∀ x : E,
      ‖fderiv ℝ
        (ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr)) x‖ ≤ C₁) :
    ∀ x : E, 0 < shiEuclideanSquaredCutoff r hr x →
      ‖fderiv ℝ (shiEuclideanSquaredCutoff r hr) x‖ ^ 2 /
          shiEuclideanSquaredCutoff r hr x ≤ 4 * C₁ ^ 2 := by
  intro x heta
  let psi : E → ℝ :=
    ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr)
  have hpsi_diff : DifferentiableAt ℝ psi x :=
    ((shiEuclideanCutoff_contDiff (E := E) hr).differentiable
      (by simp)).differentiableAt
  have hpsi_pos : 0 < psi x := by
    have hsquare : 0 < (psi x) ^ 2 := by
      simpa [psi, shiEuclideanSquaredCutoff] using heta
    nlinarith [shiEuclideanCutoff_nonneg r hr x]
  have hfderiv_raw := fderiv_pow 2 hpsi_diff
  have hfderiv :
      fderiv ℝ (shiEuclideanSquaredCutoff r hr) x =
        (2 * psi x) • fderiv ℝ psi x := by
    simpa [shiEuclideanSquaredCutoff, psi, smul_eq_mul, Nat.reduceSub] using
      hfderiv_raw
  have hnorm :
      ‖fderiv ℝ (shiEuclideanSquaredCutoff r hr) x‖ ≤
        2 * psi x * C₁ := by
    rw [hfderiv, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (hderiv x)
      (mul_nonneg (by norm_num) hpsi_pos.le)
  have hnorm_nonneg : 0 ≤ ‖fderiv ℝ (shiEuclideanSquaredCutoff r hr) x‖ :=
    norm_nonneg _
  have hbound_nonneg : 0 ≤ 2 * psi x * C₁ := by positivity
  have hsquare_bound :
      ‖fderiv ℝ (shiEuclideanSquaredCutoff r hr) x‖ ^ 2 ≤
        (2 * psi x * C₁) ^ 2 :=
    (sq_le_sq₀ hnorm_nonneg hbound_nonneg).2 hnorm
  have heta_eq : shiEuclideanSquaredCutoff r hr x = (psi x) ^ 2 := by
    rfl
  rw [heta_eq]
  apply (div_le_iff₀ (sq_pos_of_pos hpsi_pos)).2
  nlinarith

/-- The squared bump admits a nonnegative global gradient-ratio constant in
finite dimension. -/
theorem shiEuclideanSquaredCutoff_exists_gradient_ratio_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {r : ℝ} (hr : 0 < r) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ x : E,
      0 < shiEuclideanSquaredCutoff r hr x →
        ‖fderiv ℝ (shiEuclideanSquaredCutoff r hr) x‖ ^ 2 /
            shiEuclideanSquaredCutoff r hr x ≤ G := by
  obtain ⟨C₁, C₂, hC₁, _hC₂, hfirst, _hsecond⟩ :=
    shiEuclideanCutoff_exists_derivative_bounds (E := E) hr
  refine ⟨4 * C₁ ^ 2, by positivity, ?_⟩
  exact shiEuclideanSquaredCutoff_gradient_ratio_le hr hC₁ hfirst

/-- Build a `ShiParabolicCutoff` certificate from the squared bump.  The scalar
gradient field is the operator norm of its Frechet derivative, so the
quotient hypothesis is exactly the one produced above. -/
theorem shiParabolicCutoff_of_squared_euclidean_bump
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {core outer : Set E} {r L G : ℝ} (hr : 0 < r)
    {lap : E → ℝ}
    (hcore : ∀ x, x ∈ core → x ∈ Metric.closedBall (0 : E) (r / 4))
    (houter : ∀ x, x ∉ outer → x ∉ Metric.ball (0 : E) (r / 2))
    (hL : 0 ≤ L) (hG : 0 ≤ G)
    (hlap : ∀ x, |lap x| ≤ L)
    (hgrad : ∀ x, 0 < shiEuclideanSquaredCutoff (E := E) r hr x →
      ‖fderiv ℝ (shiEuclideanSquaredCutoff (E := E) r hr) x‖ ^ 2 /
          shiEuclideanSquaredCutoff (E := E) r hr x ≤ G) :
    ShiParabolicCutoff core outer
      (shiEuclideanSquaredCutoff (E := E) r hr) lap
      (fun x => ‖fderiv ℝ (shiEuclideanSquaredCutoff (E := E) r hr) x‖) L G := by
  refine
    { L_nonneg := hL
      G_nonneg := hG
      nonneg := fun x => shiEuclideanSquaredCutoff_nonneg r hr x
      bounded := fun x => shiEuclideanSquaredCutoff_le_one r hr x
      one_on_core := fun x hx => shiEuclideanSquaredCutoff_eq_one_of_mem hr (hcore x hx)
      zero_off_outer := fun x hx =>
        shiEuclideanSquaredCutoff_eq_zero_of_not_mem hr (houter x hx)
      laplacian_bound := hlap
      gradient_ratio := ?_ }
  intro x hx
  simpa using hgrad x hx

/-- Existential packaging of the squared-bump certificate when only the
Laplacian estimate is supplied separately.  The gradient-ratio constant is
constructed from smoothness and finite-dimensional compact support. -/
theorem exists_shiParabolicCutoff_of_squared_euclidean_bump
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {core outer : Set E} {r L : ℝ} (hr : 0 < r)
    {lap : E → ℝ}
    (hcore : ∀ x, x ∈ core → x ∈ Metric.closedBall (0 : E) (r / 4))
    (houter : ∀ x, x ∉ outer → x ∉ Metric.ball (0 : E) (r / 2))
    (hL : 0 ≤ L) (hlap : ∀ x, |lap x| ≤ L) :
    ∃ G : ℝ, 0 ≤ G ∧
      ShiParabolicCutoff core outer
        (shiEuclideanSquaredCutoff (E := E) r hr) lap
        (fun x => ‖fderiv ℝ (shiEuclideanSquaredCutoff (E := E) r hr) x‖) L G := by
  obtain ⟨G, hG, hgrad⟩ :=
    shiEuclideanSquaredCutoff_exists_gradient_ratio_bound (E := E) hr
  exact ⟨G, hG,
    shiParabolicCutoff_of_squared_euclidean_bump hr hcore houter hL hG hlap hgrad⟩

end MorganTianLib
