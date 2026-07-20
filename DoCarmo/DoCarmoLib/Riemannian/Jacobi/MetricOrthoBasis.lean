import Mathlib.LinearAlgebra.QuadraticForm.Basic
import DoCarmoLib.Riemannian.Metric.RiemannianMetric

/-!
# An orthonormal basis for the Riemannian metric at a point

do Carmo, *Riemannian Geometry*, Ch. 1, §2.  Every fibre `T_qM` of the tangent bundle carries
the inner product `g_q = g.metricInner q`, and a great many arguments (parallel frames along a
curve, the frame form of the Jacobi equation, E. Cartan's theorem) start by choosing an
orthonormal basis `e₁,…,eₙ` of that fibre.

`exists_metricOrthonormalBasis` supplies it **intrinsically**: at any point `q` of the manifold,
without reference to a chart.  This is the manifold-level counterpart of the chart-level
producers `exists_chartOrthonormalBasis_at` and `exists_chartOrthonormalBasis_of_mem_baseSet`,
which pin the same data to `chartMetricInner g α y`; since `TangentSpace I q` is the model space
`E`, the basis is returned as a family `Fin (finrank ℝ E) → E`.

The proof is the same diagonalize-and-normalize route as the chart-level versions, with the
`chartMetricInner` bilinearity lemmas replaced by the `RiemannianMetric` structure's own
(`metricInner_add_left`, `metricInner_smul_left`, …): package `g.metricInner q` as a
`LinearMap.BilinForm ℝ E`, diagonalize it with `LinearMap.BilinForm.exists_orthogonal_basis`
(symmetry is `metricInner_comm`), and rescale each basis vector by `⟨vᵢ, vᵢ⟩^(-1/2)`, which is
legitimate because `g` is positive-definite (`metricInner_self_pos`).  Unlike the chart-level
statements, no interiority or base-set hypothesis is needed: positive-definiteness of a
Riemannian metric holds at every point of `M`, so the statement is unconditional in `q`.
-/

open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** **An orthonormal basis for the Riemannian metric at a point.**  At every point
`q : M` the metric inner product `g.metricInner q` is a symmetric positive-definite bilinear
form on the fibre `T_qM = E`, hence admits an orthonormal basis: a family `e₁,…,eₙ` of model
vectors with `⟨eᵢ, eⱼ⟩_q = δᵢⱼ`.  This is the intrinsic (chart-free) analogue of
`exists_chartOrthonormalBasis_at`, and needs no hypothesis on `q`, since a Riemannian metric is
positive-definite at every point.

Proof: package `g.metricInner q` as a `LinearMap.BilinForm ℝ E` out of its bilinearity
(`metricInner_add_left`/`metricInner_smul_left` and their right-hand mates), diagonalize the
form with `LinearMap.BilinForm.exists_orthogonal_basis` — applicable since `metricInner_comm`
makes it symmetric — to get a basis `v` with `⟨vᵢ, vⱼ⟩_q = 0` for `i ≠ j`, and normalize each
member to `⟨vᵢ, vᵢ⟩_q^(-1/2) • vᵢ`.  The normalization is well defined because each
`⟨vᵢ, vᵢ⟩_q` is strictly positive (`metricInner_self_pos`, applied to `vᵢ ≠ 0`). -/
theorem exists_metricOrthonormalBasis (g : RiemannianMetric I M) (q : M) :
    ∃ e : Fin (Module.finrank ℝ E) → E,
      ∀ i j, g.metricInner q (e i : TangentSpace I q) (e j) = if i = j then (1 : ℝ) else 0 := by
  classical
  -- `TangentSpace I q` is only semireducibly `E`, so restate the bilinearity lemmas with
  -- `E`-typed arguments (`exact`, not `rw`, crosses the synonym) before using them to rewrite.
  have hal : ∀ a₁ a₂ b : E, g.metricInner q (a₁ + a₂) b
      = g.metricInner q a₁ b + g.metricInner q a₂ b := fun a₁ a₂ b =>
    g.metricInner_add_left q a₁ a₂ b
  have har : ∀ a b₁ b₂ : E, g.metricInner q a (b₁ + b₂)
      = g.metricInner q a b₁ + g.metricInner q a b₂ := fun a b₁ b₂ =>
    g.metricInner_add_right q a b₁ b₂
  have hsl : ∀ (c : ℝ) (a b : E), g.metricInner q (c • a) b = c * g.metricInner q a b :=
    fun c a b => g.metricInner_smul_left q c a b
  have hsr : ∀ (c : ℝ) (a b : E), g.metricInner q a (c • b) = c * g.metricInner q a b :=
    fun c a b => g.metricInner_smul_right q c a b
  set B : LinearMap.BilinForm ℝ E :=
    LinearMap.mk₂ ℝ (g.metricInner q) hal
      (fun s a b => by rw [hsl, smul_eq_mul])
      har
      (fun s a b => by rw [hsr, smul_eq_mul]) with hB
  have hBapp : ∀ a b, B a b = g.metricInner q a b := by
    intro a b; rw [hB]; rfl
  obtain ⟨v, hv⟩ : ∃ v : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E, B.IsOrthoᵢ v := by
    apply LinearMap.BilinForm.exists_orthogonal_basis
    exact ⟨fun x y => by
      simp only [hBapp]; exact g.metricInner_comm q x y⟩
  rw [LinearMap.isOrthoᵢ_def] at hv
  have hc : ∀ i, 0 < g.metricInner q (v i) (v i) := fun i =>
    g.metricInner_self_pos q (v i) (v.ne_zero i)
  refine ⟨fun i => (Real.sqrt (g.metricInner q (v i) (v i)))⁻¹ • v i, ?_⟩
  intro i j
  rw [hsl, hsr]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hsq : Real.sqrt (g.metricInner q (v i) (v i))
        * Real.sqrt (g.metricInner q (v i) (v i))
        = g.metricInner q (v i) (v i) :=
      Real.mul_self_sqrt (hc i).le
    rw [← mul_assoc, ← mul_inv, hsq, inv_mul_cancel₀ (hc i).ne']
  · rw [if_neg hij]
    have hoff := hv i j hij
    rw [hBapp] at hoff
    rw [hoff, mul_zero, mul_zero]

/-! ### Extend a `g`-unit vector to a metric-orthonormal basis -/

/-- **Math.** **A Householder reflection is a `g`-isometry at `q`.**  For a vector `w` with
`⟨w, w⟩_q ≠ 0`, the reflection `R x = x − (2⟨w, x⟩_q / ⟨w, w⟩_q)·w` across the hyperplane
`⟨w, ·⟩_q = 0` preserves the (symmetric) metric inner product: `⟨R x, R x'⟩_q = ⟨x, x'⟩_q`.
This is the intrinsic (chart-free) counterpart of `chartMetricInner_householderReflection`. -/
theorem metricInner_householderReflection (g : RiemannianMetric I M) (q : M) (w : E)
    (hw : g.metricInner q w w ≠ 0) (x x' : E) :
    g.metricInner q
        (x + (-(2 * g.metricInner q w x / g.metricInner q w w)) • w)
        (x' + (-(2 * g.metricInner q w x' / g.metricInner q w w)) • w)
      = g.metricInner q x x' := by
  simp only [g.metricInner_add_left, g.metricInner_add_right,
    g.metricInner_smul_left, g.metricInner_smul_right]
  rw [g.metricInner_comm q x w]
  field_simp
  ring

/-- **Math.** **Extend a `g`-unit vector to a metric-orthonormal basis.**  If `v` is a
`g`-unit vector at `q` (`⟨v, v⟩_q = 1`), there is a metric-orthonormal basis `e₁,…,eₙ` of the
model space (`⟨eᵢ, eⱼ⟩_q = δᵢⱼ`) and an index `n₀` with `e_{n₀} = v`.  Take a generic
metric-orthonormal basis `f` (`exists_metricOrthonormalBasis`); if `f 0 = v` we are done,
otherwise the Householder reflection `R` with `w = f 0 − v` fixes the inner product and sends
`f 0` to `v`, so `R ∘ f` is orthonormal with `(R ∘ f) 0 = v`.  This is the intrinsic
counterpart of `exists_chartOrthonormalBasis_containing_unit`; unlike it, it needs no base-set
hypothesis because a Riemannian metric is positive-definite at every point. -/
theorem exists_metricOrthonormalBasis_containing_unit [NeZero (Module.finrank ℝ E)]
    (g : RiemannianMetric I M) (q : M) {v : E} (hv : g.metricInner q v v = 1) :
    ∃ (e : Fin (Module.finrank ℝ E) → E) (n₀ : Fin (Module.finrank ℝ E)),
      e n₀ = v ∧
      ∀ i j, g.metricInner q (e i : TangentSpace I q) (e j) = if i = j then (1 : ℝ) else 0 := by
  classical
  obtain ⟨f, hf⟩ := exists_metricOrthonormalBasis (I := I) g q
  have hf00 : g.metricInner q (f 0) (f 0) = 1 := by rw [hf 0 0, if_pos rfl]
  by_cases hfv : f 0 = v
  · exact ⟨f, 0, hfv, hf⟩
  · -- Householder reflection swapping `f 0 ↦ v`
    set w : E := f 0 - v with hw
    have hwne : w ≠ 0 := sub_ne_zero.mpr hfv
    have hswpos : 0 < g.metricInner q w w := g.metricInner_self_pos q w hwne
    have hsw : g.metricInner q w w ≠ 0 := hswpos.ne'
    set R : E → E := fun x =>
      x + (-(2 * g.metricInner q w x / g.metricInner q w w)) • w with hR
    have hwf0 : g.metricInner q w (f 0) = 1 - g.metricInner q v (f 0) := by
      rw [hw, g.metricInner_sub_left, hf00]
    have hww : g.metricInner q w w = 2 - 2 * g.metricInner q v (f 0) := by
      rw [hw, g.metricInner_sub_right, g.metricInner_sub_left, g.metricInner_sub_left, hf00, hv,
        g.metricInner_comm q (f 0) v]
      ring
    have hden : (2 : ℝ) - 2 * g.metricInner q v (f 0) ≠ 0 := by rw [← hww]; exact hsw
    have hcoef : 2 * g.metricInner q w (f 0) / g.metricInner q w w = 1 := by
      rw [hwf0, hww, div_eq_one_iff_eq hden]; ring
    have hRf0 : R (f 0) = v := by
      simp only [hR]; rw [hcoef, neg_smul, one_smul, hw]; abel
    refine ⟨fun i => R (f i), 0, hRf0, ?_⟩
    intro i j
    show g.metricInner q (R (f i)) (R (f j)) = _
    simp only [hR]
    rw [metricInner_householderReflection (I := I) g q w hsw (f i) (f j)]
    exact hf i j

end Riemannian.Jacobi

end
