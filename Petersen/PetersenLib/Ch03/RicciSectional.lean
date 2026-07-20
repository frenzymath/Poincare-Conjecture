import PetersenLib.Ch03.RicciCurvature

/-!
# Petersen Ch. 3, §3.1.4 — Ricci curvature via sectional curvature

The trace formula `Ric(v,w) = ∑ᵢ R⁴(eᵢ, v, w, eᵢ)` in a `g`-orthonormal basis
(`ricciCurvature_eq_sum`), Petersen's relation
`Ric(v,v) = ∑_{i≠i₀} sec(v, eᵢ)` for a unit vector `v = e_{i₀}` completed to a
`g`-orthonormal basis (`ricciCurvature_eq_sum_sectionalCurvature`), and the
observation that constant curvature `k` forces the Einstein condition with
Einstein constant `(n-1)·k` (`constantCurvature_isEinstein`).

Along the way: the diagonal of an algebraic curvature form vanishes on
linearly dependent pairs (`IsAlgCurvatureForm.diag_eq_zero_of_not_linearIndependent`),
the strict Cauchy–Schwarz positivity `|v∧w|² > 0` for independent pairs
(`bivectorInnerProduct_self_pos`), coordinates in a `g`-orthonormal basis
(`orthonormal_basis_repr_eq_metricInner`), and the Parseval expansion of the
metric (`metricInner_eq_sum_mul`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.4.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

/-! ## Algebraic preliminaries -/

section AlgebraicCurvature

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Math.** The diagonal `B(x,y,x,y)` of an algebraic curvature form vanishes
on linearly *dependent* pairs: if `y = c•x` (or `x = 0`) then antisymmetry in
the first pair kills the value. Complements the constant-curvature diagonal
identities, which a priori only see independent pairs. -/
theorem IsAlgCurvatureForm.diag_eq_zero_of_not_linearIndependent
    {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B) {x y : V}
    (h : ¬LinearIndependent ℝ ![x, y]) : B x y x y = 0 := by
  rw [LinearIndependent.pair_iff] at h
  push Not at h
  obtain ⟨s, t, hst, hne⟩ := h
  rcases eq_or_ne s 0 with hs | hs
  · -- then `t ≠ 0` and `t • y = 0`, so `y = 0`.
    have ht : t ≠ 0 := hne hs
    rw [hs, zero_smul, zero_add] at hst
    have hy : y = 0 := by
      rcases smul_eq_zero.mp hst with h' | h'
      · exact absurd h' ht
      · exact h'
    rw [hy]
    exact hB.zero_two x x 0
  · -- then `x = (s⁻¹ * (-t)) • y`.
    obtain ⟨c, hc⟩ : ∃ c : ℝ, x = c • y := by
      refine ⟨s⁻¹ * (-t), ?_⟩
      have h1 : s • x = (-t) • y := by
        linear_combination (norm := module) hst
      calc x = (s⁻¹ * s) • x := by rw [inv_mul_cancel₀ hs, one_smul]
        _ = s⁻¹ • (s • x) := by rw [mul_smul]
        _ = s⁻¹ • ((-t) • y) := by rw [h1]
        _ = (s⁻¹ * (-t)) • y := by rw [mul_smul]
    rw [hc]
    have h1 : B (c • y) y (c • y) y = c * B y y (c • y) y :=
      hB.smul_left c y y (c • y) y
    have h2 : B y y (c • y) y = 0 := hB.self_left y (c • y) y
    rw [h1, h2, mul_zero]

end AlgebraicCurvature

/-! ## Metric preliminaries: Cauchy–Schwarz and orthonormal expansions -/

section MetricHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Strict Cauchy–Schwarz for the metric: if `v, w ∈ T_pM` are
linearly independent then the squared area
`g(v∧w, v∧w) = g(v,v)g(w,w) − g(v,w)²` is strictly positive. Proof: the vector
`u = g(v,v)•w − g(v,w)•v` is nonzero by independence, and
`g(u,u) = g(v,v)·(g(v,v)g(w,w) − g(v,w)²)` with `g(v,v) > 0`. -/
theorem bivectorInnerProduct_self_pos (g : RiemannianMetric I M) (p : M)
    {v w : TangentSpace I p} (h : LinearIndependent ℝ ![v, w]) :
    0 < bivectorInnerProduct g p v w v w := by
  have hv : v ≠ 0 := by
    intro h0
    have := (LinearIndependent.pair_iff.mp h 1 0 (by rw [h0]; module)).1
    exact one_ne_zero this
  have ha : 0 < g.metricInner p v v := g.metricInner_self_pos p v hv
  have hu : g.metricInner p v v • w - g.metricInner p v w • v ≠ 0 := by
    intro h0
    have hpq := LinearIndependent.pair_iff.mp h (-(g.metricInner p v w))
      (g.metricInner p v v) (by linear_combination (norm := module) h0)
    exact ha.ne' hpq.2
  have hq : 0 < g.metricInner p
      (g.metricInner p v v • w - g.metricInner p v w • v)
      (g.metricInner p v v • w - g.metricInner p v w • v) :=
    g.metricInner_self_pos p _ hu
  have hexp : g.metricInner p
      (g.metricInner p v v • w - g.metricInner p v w • v)
      (g.metricInner p v v • w - g.metricInner p v w • v)
      = g.metricInner p v v * (g.metricInner p v v * g.metricInner p w w
          - g.metricInner p v w * g.metricInner p v w) := by
    simp only [g.metricInner_sub_left, g.metricInner_sub_right,
      g.metricInner_smul_left, g.metricInner_smul_right]
    rw [g.metricInner_comm p w v]
    ring
  rw [hexp] at hq
  rw [bivectorInnerProduct, g.metricInner_comm p w v]
  nlinarith [hq, ha]

/-- **Math.** The complement of `bivectorInnerProduct_self_pos`: the squared area
`g(v∧w, v∧w) = g(v,v)g(w,w) − g(v,w)²` *vanishes* on linearly **dependent** pairs,
i.e. exactly in the Cauchy–Schwarz equality case. Proof: `bivectorPairing` of the
metric is the model algebraic curvature form
(`isAlgCurvatureForm_bivectorPairing`), and the diagonal of any algebraic
curvature form kills dependent pairs
(`IsAlgCurvatureForm.diag_eq_zero_of_not_linearIndependent`), so no separate
Cauchy–Schwarz argument is needed.

Together with `bivectorInnerProduct_self_pos` this gives the exhaustive
dichotomy that lets a `by_cases` on `LinearIndependent ℝ ![v, w]` discharge
*unconditional* statements about `sectionalCurvature`, whose denominator is
this quantity: on the dependent branch the denominator is `0`, so
`sectionalCurvature` is `0` by Lean's `div_zero` junk convention. That is the
route by which `Ch06/SecBounds.lean`'s `HasSecIn.abs_sectionalCurvature_le`
meets `exercise3_4_30`'s unconditional `∀ v w, |sec| ≤ k` hypothesis. -/
theorem bivectorInnerProduct_self_eq_zero_of_not_linearIndependent
    (g : RiemannianMetric I M) (p : M) {v w : TangentSpace I p}
    (h : ¬ LinearIndependent ℝ ![v, w]) :
    bivectorInnerProduct g p v w v w = 0 :=
  (isAlgCurvatureForm_bivectorPairing (g.metricBilin p)
    (fun a b => g.metricInner_comm p a b)).diag_eq_zero_of_not_linearIndependent h

/-- **Math.** The squared area `g(v∧w, v∧w)` is always nonnegative — the
(non-strict) Cauchy–Schwarz inequality for `g`, obtained by combining the
strict positivity on independent pairs with the vanishing on dependent ones. -/
theorem bivectorInnerProduct_self_nonneg (g : RiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) : 0 ≤ bivectorInnerProduct g p v w v w := by
  by_cases h : LinearIndependent ℝ ![v, w]
  · exact (bivectorInnerProduct_self_pos g p h).le
  · exact (bivectorInnerProduct_self_eq_zero_of_not_linearIndependent g p h).ge

/-- Finite sums pull out of the first slot of the metric. -/
theorem metricInner_sum_smul_left (g : RiemannianMetric I M) (p : M)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → TangentSpace I p)
    (w : TangentSpace I p) :
    g.metricInner p (∑ i ∈ s, c i • f i) w
      = ∑ i ∈ s, c i * g.metricInner p (f i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, g.metricInner_add_left,
        g.metricInner_smul_left, ih, Finset.sum_insert ha]

/-- **Math.** Coordinates in a `g`-orthonormal basis are metric pairings:
`x = ∑ᵢ g(x, eᵢ)·eᵢ`, i.e. `(repr x)ᵢ = g(x, eᵢ)`. -/
theorem orthonormal_basis_repr_eq_metricInner {g : RiemannianMetric I M}
    (p : M) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I p))
    (hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0)
    (x : TangentSpace I p) (i : ι) :
    b.repr x i = g.metricInner p x (b i) := by
  conv_rhs => rw [← b.sum_repr x]
  rw [metricInner_sum_smul_left]
  simp only [hb]
  simp

/-- **Math.** Parseval expansion of the metric in a `g`-orthonormal basis:
`g(v,w) = ∑ᵢ g(v,eᵢ)·g(eᵢ,w)`. -/
theorem metricInner_eq_sum_mul {g : RiemannianMetric I M} (p : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I p))
    (hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0)
    (v w : TangentSpace I p) :
    g.metricInner p v w
      = ∑ i, g.metricInner p v (b i) * g.metricInner p (b i) w := by
  conv_lhs => rw [← b.sum_repr v]
  rw [metricInner_sum_smul_left]
  exact Finset.sum_congr rfl fun i _ => by
    rw [orthonormal_basis_repr_eq_metricInner p b hb]

end MetricHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-! ## The trace formula for the Ricci curvature -/

/-- **Math.** The **trace formula for the Ricci curvature** (Petersen §3.1.4):
in a `g`-orthonormal basis `e₁, …, eₙ` of `T_pM`,
`Ric(v,w) = tr(x ↦ R(x,v)w) = ∑ᵢ g(R(eᵢ,v)w, eᵢ) = ∑ᵢ R⁴(eᵢ, v, w, eᵢ)`. -/
theorem ricciCurvature_eq_sum {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (p : M) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℝ (TangentSpace I p))
    (hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0)
    (v w : TangentSpace I p) :
    RicciCurvature D.toAffineConnection p v w
      = ∑ i, curvatureTensorFourAt D p (b i) v w (b i) := by
  rw [RicciCurvature, LinearMap.trace_eq_matrix_trace ℝ b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    curvatureTensorAtFirstLinear_apply]
  exact Finset.sum_congr rfl fun i _ => by
    rw [orthonormal_basis_repr_eq_metricInner p b hb]
    rfl

/-! ## Ricci curvature as a sum of sectional curvatures -/

/-- **Math.** **Ricci curvature via sectional curvature** (Petersen §3.1.4):
if `v = e_{i₀}` is a unit vector completed to a `g`-orthonormal basis
`e₁, …, eₙ` of `T_pM`, then `Ric(v,v) = ∑_{i ≠ i₀} sec(v, eᵢ)`. Indeed
`Ric(v,v) = ∑ᵢ R⁴(eᵢ, v, v, eᵢ)` by the trace formula; the `i = i₀` term
vanishes by antisymmetry, and for `i ≠ i₀` the pair `(v, eᵢ)` is orthonormal,
so `|v ∧ eᵢ|² = 1` and `sec(v, eᵢ) = R⁴(eᵢ, v, v, eᵢ)`. -/
theorem ricciCurvature_eq_sum_sectionalCurvature {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (p : M) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℝ (TangentSpace I p))
    (hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0)
    (i₀ : ι) :
    RicciCurvature D.toAffineConnection p (b i₀) (b i₀)
      = ∑ i ∈ Finset.univ.erase i₀, sectionalCurvature D p (b i₀) (b i) := by
  rw [ricciCurvature_eq_sum D p b hb (b i₀) (b i₀),
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀)]
  have hzero : curvatureTensorFourAt D p (b i₀) (b i₀) (b i₀) (b i₀) = 0 :=
    (isAlgCurvatureForm_curvatureTensorFourAt D p).self_left (b i₀) (b i₀) (b i₀)
  rw [hzero, zero_add]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hne : i ≠ i₀ := Finset.ne_of_mem_erase hi
  rw [sectionalCurvature_eq_curvatureTensorFourAt]
  have hbiv : bivectorInnerProduct g p (b i₀) (b i) (b i₀) (b i) = 1 := by
    simp only [bivectorInnerProduct, hb]
    simp [hne, Ne.symm hne]
  rw [hbiv, div_one]

/-! ## Constant curvature implies Einstein -/

/-- **Math.** **Constant curvature implies Einstein** (Petersen §3.1.4): if
`(M,g)` has constant curvature `k` then it is Einstein with Einstein constant
`(n−1)·k`, where `n = dim M`. From `sec ≡ k` and strict Cauchy–Schwarz, the
diagonal identity `R⁴(x,y,x,y) = −k·g(x∧y, x∧y)` holds for all pairs
(dependent pairs contribute `0 = 0`), so do Carmo's Lemma 3.4 upgrades it to
the full tensor identity `R⁴ = −k·g(·∧·, ·∧·)`; tracing in a `g`-orthonormal
basis via Parseval yields `Ric(v,w) = (n−1)·k·g(v,w)`. -/
theorem constantCurvature_isEinstein {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {k : ℝ} (h : HasConstantCurvature D k) :
    IsEinstein D (((Module.finrank ℝ E : ℝ) - 1) * k) := by
  intro p v w
  classical
  have halg := isAlgCurvatureForm_curvatureTensorFourAt D p
  have hG : ∀ a b : TangentSpace I p,
      g.metricBilin p a b = g.metricBilin p b a :=
    fun a b => g.metricInner_comm p a b
  have hpair := isAlgCurvatureForm_bivectorPairing (g.metricBilin p) hG
  -- Step 1: the diagonal identity `R⁴(x,y,x,y) = −k·g(x∧y,x∧y)` for all pairs.
  have hdiag : ∀ x y : TangentSpace I p, curvatureTensorFourAt D p x y x y
      = -k * bivectorPairing (g.metricBilin p) x y x y := by
    intro x y
    by_cases hxy : LinearIndependent ℝ ![y, x]
    · have hsec := h p y x hxy
      rw [sectionalCurvature_eq_curvatureTensorFourAt] at hsec
      have hpos : 0 < bivectorInnerProduct g p y x y x :=
        bivectorInnerProduct_self_pos g p hxy
      rw [div_eq_iff hpos.ne'] at hsec
      have h34 : curvatureTensorFourAt D p x y x y
          = -curvatureTensorFourAt D p x y y x := halg.antisymm₃₄ x y x y
      rw [h34, hsec, bivectorInnerProduct_eq_bivectorPairing]
      simp only [bivectorPairing, RiemannianMetric.metricBilin_apply]
      ring
    · have hxy' : ¬LinearIndependent ℝ ![x, y] := fun hLI =>
        hxy (LinearIndependent.pair_symm_iff.mp hLI)
      have hL : curvatureTensorFourAt D p x y x y = 0 :=
        halg.diag_eq_zero_of_not_linearIndependent hxy'
      have hR : bivectorPairing (g.metricBilin p) x y x y = 0 :=
        hpair.diag_eq_zero_of_not_linearIndependent hxy'
      rw [hL, hR, mul_zero]
  -- Step 2: upgrade to the full tensor identity (do Carmo Lemma 3.4).
  have hfull := halg.eq_smul_bivectorPairing_of_const (g.metricBilin p) hG
    (-k) hdiag
  -- Step 3: trace in a `g`-orthonormal basis.
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set b := stdOrthonormalBasis ℝ (TangentSpace I p) with hbdef
  have hb : ∀ i j, g.metricInner p (b.toBasis i) (b.toBasis j)
      = if i = j then 1 else 0 := by
    intro i j
    have h1 := orthonormal_iff_ite.mp b.orthonormal i j
    rw [OrthonormalBasis.coe_toBasis]
    exact h1
  rw [ricciCurvature_eq_sum D p b.toBasis hb v w]
  have hsum : ∑ i, curvatureTensorFourAt D p (b.toBasis i) v w (b.toBasis i)
      = ∑ i, -k * (g.metricInner p v (b.toBasis i)
          * g.metricInner p (b.toBasis i) w - g.metricInner p v w) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hf : curvatureTensorFourAt D p (b.toBasis i) v w (b.toBasis i)
        = -k * bivectorPairing (g.metricBilin p) (b.toBasis i) v w
            (b.toBasis i) := hfull _ v w _
    have hbii : g.metricInner p (b.toBasis i) (b.toBasis i) = 1 := by
      rw [hb i i, if_pos rfl]
    rw [hf]
    simp only [bivectorPairing, RiemannianMetric.metricBilin_apply, hbii]
    ring
  rw [hsum, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← metricInner_eq_sum_mul p b.toBasis hb v w, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
  have hfr : Module.finrank ℝ (TangentSpace I p) = Module.finrank ℝ E := rfl
  rw [hfr]
  ring

end PetersenLib
