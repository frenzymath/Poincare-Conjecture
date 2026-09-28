import MorganTianLib.Ch02.LaplacianCoord
import MorganTianLib.Ch02.Bochner
import MorganTianLib.Ch02.CovDerivAlongCurve

/-!
# Morgan–Tian Ch. 2 — the parallel gradient field in a fixed chart

Blueprint `lem:parallel-gradient-flow`(4), chart-level engine. Under the
Bochner package (`|∇f|² ≡ c₁`, `Δf ≡ c₂`, `Ric(∇f,∇f) ≥ 0`) the gradient
field `V = (∇f)^*` is parallel (`Hess f ≡ 0`, Bochner.lean). This file
expresses that parallelism in a **fixed chart at arbitrary chart points** —
the form consumed by the variational equation of the gradient flow, where a
whole trajectory is analyzed in one chart:

* `sum_chartGramOnE_mul_chartCoord_fieldChartRep_gradientField` — the chart
  **Riesz identity** `∑_j G_{ij}(y) V̂^j(y) = ∂_i F(y)`, `F = f ∘ φ⁻¹`: the
  chart representation of the gradient is the Gram-dual of the coordinate
  differential, at every point of the chart target.
* `contDiffOn_fieldChartRep_gradientField` — hence `V̂ = G⁻¹ dF` is smooth on
  the chart target.
* `fderiv_fieldChartRep_gradientField_of_bochner` — the **fixed-chart
  parallel identity** `∂V̂(y)·w = −Γ(w, V̂(y))(y)` at every chart-target
  point and in every direction. Derived by differentiating the Riesz
  identity: `∂_k∂_i F = Σ_m Γ^m_{ki} ∂_m F` (the chart Hessian formula
  `hessianAt_chartBasisVecFiber` + Bochner vanishing) together with the
  chart metric-compatibility `partialDeriv_chartGramOnE_eq` and
  non-degeneracy of the Gram matrix. No Christoffel transformation law is
  needed: everything happens in one chart.
* `covariantDerivCoord_variational_gradientField_eq_zero` — consequently a
  solution `d` of the **variational equation** `d' = ∂V̂(u)·d` along a chart
  flow line `u' = V̂(u)` is a parallel coordinate field: `d' + Γ(u', d) = 0`.
* `chartMetricInner_variational_gradientField_eq_left` — hence the chart
  Gram inner product `⟨d₁, d₂⟩_{G(u(t))}` of two variational solutions is
  **constant in `t`** — the chart-level heart of the θ_t-isometry claim of
  blueprint `lem:parallel-gradient-flow`(4).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4
(blueprint `lem:parallel-gradient-flow`).
-/

open Set Filter Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** Kronecker collapse: `∑_j δ_{ij} c_j = c_i`. -/
private theorem sum_ite_eq_mul_left {n : ℕ} (i : Fin n) (c : Fin n → ℝ) :
    ∑ j, (if i = j then (1 : ℝ) else 0) * c j = c i := by
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, one_mul]
  · intro a _ ha
    rw [if_neg fun h => ha h.symm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **Math.** Coordinates of a model basis vector: `(e_i)^a = δ_{ia}`. -/
private theorem chartCoord_finBasis (i a : Fin (Module.finrank ℝ E)) :
    Geodesic.chartCoord (E := E) a ((Module.finBasis ℝ E) i)
      = (if i = a then (1 : ℝ) else 0) := by
  rw [Geodesic.chartCoord_def, Module.Basis.repr_self]
  exact Finsupp.single_apply

/-! ### The coordinate representation of a smooth function on the chart target -/

/-- **Math.** The coordinate representation `F = f ∘ φ⁻¹` of a smooth function
is smooth at every point of the chart target. -/
theorem contDiffAt_comp_extChartAt_symm {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (z : M) {y : E}
    (hy : y ∈ (extChartAt I z).target) :
    ContDiffAt ℝ ∞ (f ∘ (extChartAt I z).symm) y := by
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I z).symm y :=
    (contMDiffOn_extChartAt_symm (I := I) z).contMDiffAt
      ((isOpen_extChartAt_target (I := I) z).mem_nhds hy)
  exact contMDiffAt_iff_contDiffAt.mp
    (ContMDiffAt.comp y (hf ((extChartAt I z).symm y)) hsymm)

/-- **Math.** The coordinate representation `F = f ∘ φ⁻¹` of a smooth function
is smooth on the chart target. -/
theorem contDiffOn_comp_extChartAt_symm {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (z : M) :
    ContDiffOn ℝ ∞ (f ∘ (extChartAt I z).symm) (extChartAt I z).target :=
  fun _ hy => (contDiffAt_comp_extChartAt_symm hf z hy).contDiffWithinAt

/-! ### The chart Riesz identity: `G · V̂ = dF` on the chart target -/

/-- **Math.** **The chart Riesz identity for the gradient**: at every point
`y` of the chart target, the Gram pairing of the chart representation
`V̂ = fieldChartRep z (∇f)^*` with the `i`-th coordinate direction is the
`i`-th coordinate partial of `F = f ∘ φ⁻¹`:
`∑_j G_{ij}(y)\, V̂^j(y) = ∂_i F(y)`. This is `⟨(∇f)^*, ∂_i⟩ = ∂_i(f)` read
through the chart trivialization. Blueprint `lem:parallel-gradient-flow`. -/
theorem sum_chartGramOnE_mul_chartCoord_fieldChartRep_gradientField
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (z : M) {y : E}
    (hy : y ∈ (extChartAt I z).target) (i : Fin (Module.finrank ℝ E)) :
    ∑ j, chartGramOnE (I := I) g z i j y
        * Geodesic.chartCoord (E := E) j
            (fieldChartRep (I := I) z (gradientField g f hf) y)
      = partialDeriv (E := E) i (f ∘ (extChartAt I z).symm) y := by
  classical
  set q : M := (extChartAt I z).symm y with hq_def
  have hqsrc : q ∈ (extChartAt I z).source := (extChartAt I z).map_target hy
  have hqchart : q ∈ (chartAt H z).source := by rwa [extChartAt_source] at hqsrc
  have hqbase : q ∈ (trivializationAt E (TangentSpace I) z).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  have hyq : extChartAt I z q = y := (extChartAt I z).right_inv hy
  -- the metric pairing of the chart frame vector with the gradient is `∂_i F`
  have hpair : g.metricInner q (Tensor.chartBasisVecFiber (I := I) z i q)
        (gradientAt g f q)
      = partialDeriv (E := E) i (f ∘ (extChartAt I z).symm) y := by
    rw [g.metricInner_comm, metricInner_gradientAt, ← hyq]
    exact mfderiv_apply_chartBasisVecFiber (hf q) z hqchart i
  -- read the pairing through the chart trivialization
  rw [metricInner_eq_chartMetricInner (I := I) g z hqchart] at hpair
  have hframe : chartFiberCoord (I := I) z
        ⟨q, Tensor.chartBasisVecFiber (I := I) z i q⟩
      = (Module.finBasis ℝ E) i :=
    Tensor.trivializationAt_chartBasisVec_snd (I := I) z i hqbase
  have hgradrep : chartFiberCoord (I := I) z ⟨q, gradientAt g f q⟩
      = fieldChartRep (I := I) z (gradientField g f hf) y := rfl
  rw [hframe, hgradrep, hyq, chartMetricInner_def] at hpair
  -- collapse the frame index against the basis vector's coordinates
  have hcollapse : (∑ a, ∑ j, chartGramOnE (I := I) g z a j y
        * Geodesic.chartCoord (E := E) a ((Module.finBasis ℝ E) i)
        * Geodesic.chartCoord (E := E) j
          (fieldChartRep (I := I) z (gradientField g f hf) y))
      = ∑ j, chartGramOnE (I := I) g z i j y
        * Geodesic.chartCoord (E := E) j
          (fieldChartRep (I := I) z (gradientField g f hf) y) := by
    calc (∑ a, ∑ j, chartGramOnE (I := I) g z a j y
          * Geodesic.chartCoord (E := E) a ((Module.finBasis ℝ E) i)
          * Geodesic.chartCoord (E := E) j
            (fieldChartRep (I := I) z (gradientField g f hf) y))
        = ∑ a, (if i = a then (1 : ℝ) else 0)
            * ∑ j, chartGramOnE (I := I) g z a j y
              * Geodesic.chartCoord (E := E) j
                (fieldChartRep (I := I) z (gradientField g f hf) y) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [chartCoord_finBasis i a]
          ring
      _ = _ := sum_ite_eq_mul_left i _
  rw [hcollapse] at hpair
  exact hpair

/-! ### Non-degeneracy of the chart Gram matrix -/

/-- **Math.** **Non-degeneracy of the Gram matrix on the chart target**: a
coordinate vector whose Gram pairing with every coordinate direction
vanishes is zero. -/
theorem eq_zero_of_forall_sum_chartGramOnE_mul_chartCoord_eq_zero
    (g : RiemannianMetric I M) (z : M) {y : E}
    (hy : y ∈ (extChartAt I z).target) {w : E}
    (hw : ∀ i, ∑ j, chartGramOnE (I := I) g z i j y
        * Geodesic.chartCoord (E := E) j w = 0) : w = 0 := by
  classical
  set q : M := (extChartAt I z).symm y with hq_def
  have hqsrc : q ∈ (extChartAt I z).source := (extChartAt I z).map_target hy
  have hqbase : q ∈ (trivializationAt E (TangentSpace I) z).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source, ← extChartAt_source (I := I)]
    exact hqsrc
  have hinv := Tensor.chartInvGramMatrix_mul_chartGramMatrix (I := I) g z hqbase
  have hentry : ∀ k j, (∑ i, Tensor.chartInvGramMatrix (I := I) g z q k i
        * Tensor.chartGramMatrix (I := I) g z q i j)
      = if k = j then (1 : ℝ) else 0 := by
    intro k j
    have h1 : (Tensor.chartInvGramMatrix (I := I) g z q
          * Tensor.chartGramMatrix (I := I) g z q) k j
        = (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) k j := by
      rw [hinv]
    rwa [Matrix.mul_apply, Matrix.one_apply] at h1
  -- every coordinate of `w` vanishes, by inverting the Gram matrix
  have hcoord : ∀ k, Geodesic.chartCoord (E := E) k w = 0 := by
    intro k
    calc Geodesic.chartCoord (E := E) k w
        = ∑ j, (if k = j then (1 : ℝ) else 0) * Geodesic.chartCoord (E := E) j w :=
          (sum_ite_eq_mul_left k _).symm
      _ = ∑ j, (∑ i, Tensor.chartInvGramMatrix (I := I) g z q k i
            * Tensor.chartGramMatrix (I := I) g z q i j)
            * Geodesic.chartCoord (E := E) j w := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hentry k j]
      _ = ∑ j, ∑ i, Tensor.chartInvGramMatrix (I := I) g z q k i
            * Tensor.chartGramMatrix (I := I) g z q i j
            * Geodesic.chartCoord (E := E) j w := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ i, ∑ j, Tensor.chartInvGramMatrix (I := I) g z q k i
            * Tensor.chartGramMatrix (I := I) g z q i j
            * Geodesic.chartCoord (E := E) j w := Finset.sum_comm
      _ = ∑ i, Tensor.chartInvGramMatrix (I := I) g z q k i
            * ∑ j, chartGramOnE (I := I) g z i j y
              * Geodesic.chartCoord (E := E) j w := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [chartGramOnE_def]
          ring
      _ = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [hw i, mul_zero]
  -- a vector with vanishing coordinates is zero
  have hrepr := (Module.finBasis ℝ E).sum_repr w
  rw [← hrepr]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hcc : (Module.finBasis ℝ E).repr w k = Geodesic.chartCoord (E := E) k w := rfl
  rw [hcc, hcoord k, zero_smul]

/-! ### Smoothness of the chart representation of the gradient -/

/-- **Math.** Solved form of the chart Riesz identity: the `k`-th chart
coordinate of the gradient is `V̂^k = ∑_i g^{ki} ∂_i F` on the chart target. -/
theorem chartCoord_fieldChartRep_gradientField_eq_sum
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (z : M) {y : E}
    (hy : y ∈ (extChartAt I z).target) (k : Fin (Module.finrank ℝ E)) :
    Geodesic.chartCoord (E := E) k
        (fieldChartRep (I := I) z (gradientField g f hf) y)
      = ∑ i, chartInvGramOnE (I := I) g z k i y
          * partialDeriv (E := E) i (f ∘ (extChartAt I z).symm) y := by
  classical
  set q : M := (extChartAt I z).symm y with hq_def
  have hqsrc : q ∈ (extChartAt I z).source := (extChartAt I z).map_target hy
  have hqbase : q ∈ (trivializationAt E (TangentSpace I) z).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source, ← extChartAt_source (I := I)]
    exact hqsrc
  have hinv := Tensor.chartInvGramMatrix_mul_chartGramMatrix (I := I) g z hqbase
  have hentry : ∀ j, (∑ i, Tensor.chartInvGramMatrix (I := I) g z q k i
        * Tensor.chartGramMatrix (I := I) g z q i j)
      = if k = j then (1 : ℝ) else 0 := by
    intro j
    have h1 : (Tensor.chartInvGramMatrix (I := I) g z q
          * Tensor.chartGramMatrix (I := I) g z q) k j
        = (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) k j := by
      rw [hinv]
    rwa [Matrix.mul_apply, Matrix.one_apply] at h1
  calc Geodesic.chartCoord (E := E) k
        (fieldChartRep (I := I) z (gradientField g f hf) y)
      = ∑ j, (if k = j then (1 : ℝ) else 0) * Geodesic.chartCoord (E := E) j
          (fieldChartRep (I := I) z (gradientField g f hf) y) :=
        (sum_ite_eq_mul_left k _).symm
    _ = ∑ j, (∑ i, Tensor.chartInvGramMatrix (I := I) g z q k i
          * Tensor.chartGramMatrix (I := I) g z q i j)
          * Geodesic.chartCoord (E := E) j
            (fieldChartRep (I := I) z (gradientField g f hf) y) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hentry j]
    _ = ∑ j, ∑ i, Tensor.chartInvGramMatrix (I := I) g z q k i
          * Tensor.chartGramMatrix (I := I) g z q i j
          * Geodesic.chartCoord (E := E) j
            (fieldChartRep (I := I) z (gradientField g f hf) y) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ i, ∑ j, Tensor.chartInvGramMatrix (I := I) g z q k i
          * Tensor.chartGramMatrix (I := I) g z q i j
          * Geodesic.chartCoord (E := E) j
            (fieldChartRep (I := I) z (gradientField g f hf) y) := Finset.sum_comm
    _ = ∑ i, Tensor.chartInvGramMatrix (I := I) g z q k i
          * ∑ j, chartGramOnE (I := I) g z i j y
            * Geodesic.chartCoord (E := E) j
              (fieldChartRep (I := I) z (gradientField g f hf) y) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [chartGramOnE_def]
        ring
    _ = ∑ i, chartInvGramOnE (I := I) g z k i y
          * partialDeriv (E := E) i (f ∘ (extChartAt I z).symm) y := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [sum_chartGramOnE_mul_chartCoord_fieldChartRep_gradientField g hf z hy i,
          chartInvGramOnE_def]

/-- **Math.** The chart representation of the gradient field is the vector
`∑_k (∑_i g^{ki} ∂_i F) e_k` on the chart target. -/
theorem fieldChartRep_gradientField_eq_sum
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (z : M) {y : E}
    (hy : y ∈ (extChartAt I z).target) :
    fieldChartRep (I := I) z (gradientField g f hf) y
      = ∑ k, (∑ i, chartInvGramOnE (I := I) g z k i y
          * partialDeriv (E := E) i (f ∘ (extChartAt I z).symm) y)
          • (Module.finBasis ℝ E) k := by
  conv_lhs => rw [← (Module.finBasis ℝ E).sum_repr
    (fieldChartRep (I := I) z (gradientField g f hf) y)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← chartCoord_fieldChartRep_gradientField_eq_sum g hf z hy k]
  rfl

/-- **Math.** The chart representation `V̂ = G⁻¹ dF` of the gradient field is
`C^∞` on the chart target. -/
theorem contDiffOn_fieldChartRep_gradientField
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (z : M) :
    ContDiffOn ℝ ∞ (fieldChartRep (I := I) z (gradientField g f hf))
      (extChartAt I z).target := by
  have hopen : IsOpen (extChartAt I z).target := isOpen_extChartAt_target (I := I) z
  have hF : ContDiffOn ℝ ∞ (f ∘ (extChartAt I z).symm) (extChartAt I z).target :=
    contDiffOn_comp_extChartAt_symm hf z
  have hdF : ∀ i : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun y => partialDeriv (E := E) i (f ∘ (extChartAt I z).symm) y)
      (extChartAt I z).target := by
    intro i
    have hfd : ContDiffOn ℝ ∞ (fderiv ℝ (f ∘ (extChartAt I z).symm))
        (extChartAt I z).target :=
      hF.fderiv_of_isOpen hopen (by exact_mod_cast le_top)
    exact hfd.clm_apply contDiffOn_const
  have hcand : ContDiffOn ℝ ∞
      (fun y => ∑ k, (∑ i, chartInvGramOnE (I := I) g z k i y
          * partialDeriv (E := E) i (f ∘ (extChartAt I z).symm) y)
          • (Module.finBasis ℝ E) k)
      (extChartAt I z).target := by
    refine ContDiffOn.sum fun k _ => ContDiffOn.smul ?_ contDiffOn_const
    exact ContDiffOn.sum fun i _ =>
      (chartInvGramOnE_contDiffOn (I := I) g z k i).mul (hdF i)
  exact hcand.congr fun y hy => fieldChartRep_gradientField_eq_sum g hf z hy

/-! ### The second-derivative identity under the Bochner package -/

/-- **Math.** Under the Bochner package the coordinate Hessian reduces to the
first-order Christoffel term: `∂_k ∂_i F = ∑_m Γ^m_{ki} ∂_m F` at every point
of the chart target (`Hess f ≡ 0` read in the fixed chart). -/
theorem partialDeriv_partialDeriv_comp_of_bochner
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (z : M) {y : E} (hy : y ∈ (extChartAt I z).target)
    (k i : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) k
        (fun y' => partialDeriv (E := E) i (f ∘ (extChartAt I z).symm) y') y
      = ∑ m, chartChristoffel (I := I) g z k i m y
          * partialDeriv (E := E) m (f ∘ (extChartAt I z).symm) y := by
  set q : M := (extChartAt I z).symm y with hq_def
  have hqsrc : q ∈ (extChartAt I z).source := (extChartAt I z).map_target hy
  have hqchart : q ∈ (chartAt H z).source := by rwa [extChartAt_source] at hqsrc
  have hyq : extChartAt I z q = y := (extChartAt I z).right_inv hy
  -- the given Levi-Civita connection is the canonical one
  have hLC' : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W p => g.koszulDualSection_dual X Y W p)
  have hEqn : nabla = g.leviCivitaConnection :=
    AffineConnection.leviCivita_unique' g nabla g.leviCivitaConnection hLC hLC'
  -- Bochner vanishing of the Hessian, transported to the canonical connection
  have hzero : hessianAt g.leviCivitaConnection f q
      (Tensor.chartBasisVecFiber (I := I) z k q)
      (Tensor.chartBasisVecFiber (I := I) z i q) = 0 := by
    rw [← hEqn]
    exact hessianAt_eq_zero_of_bochner g hLC hf q hgrad hharm (hric q) _ _
  have hchart := hessianAt_chartBasisVecFiber (I := I) g hf hqchart k i
  rw [hzero, hyq] at hchart
  linarith [hchart]

/-! ### The fixed-chart parallel identity -/

/-- **Math.** **The fixed-chart parallel identity for the gradient field**
(blueprint `lem:parallel-gradient-flow`(1), chart form): under the Bochner
package, at every point `y` of the chart target and in every direction `w`,
`∂V̂(y)·w = −Γ(w, V̂(y))(y)` — the chart representation of the gradient field
solves the parallel-transport equation in **all** directions, not only along
a given curve. Obtained by differentiating the chart Riesz identity
`G·V̂ = dF` and cancelling with the Bochner-vanishing Hessian and the chart
metric compatibility `∂G = Γᵀ·G + G·Γ`. -/
theorem fderiv_fieldChartRep_gradientField_of_bochner
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (z : M) {y : E} (hy : y ∈ (extChartAt I z).target) (w : E) :
    fderiv ℝ (fieldChartRep (I := I) z (gradientField g f hf)) y w
      = - Geodesic.chartChristoffelContraction (I := I) g z w
          (fieldChartRep (I := I) z (gradientField g f hf) y) y := by
  classical
  have hopen : IsOpen (extChartAt I z).target := isOpen_extChartAt_target (I := I) z
  have hbase : (extChartAt I z).symm y
      ∈ (trivializationAt E (TangentSpace I) z).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source, ← extChartAt_source (I := I)]
    exact (extChartAt I z).map_target hy
  -- differentiability inventory at `y`
  have hVdiff : DifferentiableAt ℝ
      (fieldChartRep (I := I) z (gradientField g f hf)) y :=
    ((contDiffOn_fieldChartRep_gradientField g hf z).contDiffAt
      (hopen.mem_nhds hy)).differentiableAt (by simp)
  have hVjdiff : ∀ j : Fin (Module.finrank ℝ E), DifferentiableAt ℝ
      (fun y' => Geodesic.chartCoord (E := E) j
        (fieldChartRep (I := I) z (gradientField g f hf) y')) y := by
    intro j
    exact (Geodesic.chartCoordFunctional (E := E) j).differentiableAt.comp y hVdiff
  have hGdiff : ∀ i j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartGramOnE (I := I) g z i j) y := by
    intro i j
    exact ((chartGramOnE_contDiffOn (I := I) g z i j).contDiffAt
      (hopen.mem_nhds hy)).differentiableAt (by simp)
  -- the coordinate of the derivative is the derivative of the coordinate
  have hcoord_fderiv : ∀ (j : Fin (Module.finrank ℝ E)) (v : E),
      Geodesic.chartCoord (E := E) j
        (fderiv ℝ (fieldChartRep (I := I) z (gradientField g f hf)) y v)
      = fderiv ℝ (fun y' => Geodesic.chartCoord (E := E) j
          (fieldChartRep (I := I) z (gradientField g f hf) y')) y v := by
    intro j v
    have hcomp := ((Geodesic.chartCoordFunctional (E := E) j).hasFDerivAt.comp y
      hVdiff.hasFDerivAt).fderiv
    rw [show (fun y' => Geodesic.chartCoord (E := E) j
        (fieldChartRep (I := I) z (gradientField g f hf) y'))
        = (Geodesic.chartCoordFunctional (E := E) j)
          ∘ (fieldChartRep (I := I) z (gradientField g f hf)) from rfl, hcomp]
    rfl
  -- Step 1: the identity in each basis direction
  have hbasisdir : ∀ k : Fin (Module.finrank ℝ E),
      fderiv ℝ (fieldChartRep (I := I) z (gradientField g f hf)) y
        ((Module.finBasis ℝ E) k)
      + Geodesic.chartChristoffelContraction (I := I) g z ((Module.finBasis ℝ E) k)
          (fieldChartRep (I := I) z (gradientField g f hf) y) y = 0 := by
    intro k
    apply eq_zero_of_forall_sum_chartGramOnE_mul_chartCoord_eq_zero g z hy
    intro i
    -- the Gram-paired function `m_i = ∑_j G_{ij} V̂^j` agrees with `∂_i F` near `y`
    have hmeq : (fun y' => ∑ j, chartGramOnE (I := I) g z i j y'
          * Geodesic.chartCoord (E := E) j
            (fieldChartRep (I := I) z (gradientField g f hf) y'))
        =ᶠ[𝓝 y] (fun y' => partialDeriv (E := E) i (f ∘ (extChartAt I z).symm) y') := by
      filter_upwards [hopen.mem_nhds hy] with y' hy'
      exact sum_chartGramOnE_mul_chartCoord_fieldChartRep_gradientField g hf z hy' i
    -- differentiate the identity in the direction `e_k`
    have hdm : partialDeriv (E := E) k
        (fun y' => ∑ j, chartGramOnE (I := I) g z i j y'
          * Geodesic.chartCoord (E := E) j
            (fieldChartRep (I := I) z (gradientField g f hf) y')) y
        = ∑ m, chartChristoffel (I := I) g z k i m y
            * partialDeriv (E := E) m (f ∘ (extChartAt I z).symm) y := by
      rw [partialDeriv_congr_of_eventuallyEq hmeq k]
      exact partialDeriv_partialDeriv_comp_of_bochner g hLC hf hgrad hharm hric
        z hy k i
    -- product rule for the Gram-paired function
    have hterm : ∀ j : Fin (Module.finrank ℝ E), HasFDerivAt
        (fun y' => chartGramOnE (I := I) g z i j y'
          * Geodesic.chartCoord (E := E) j
            (fieldChartRep (I := I) z (gradientField g f hf) y'))
        (chartGramOnE (I := I) g z i j y
            • fderiv ℝ (fun y' => Geodesic.chartCoord (E := E) j
              (fieldChartRep (I := I) z (gradientField g f hf) y')) y
          + Geodesic.chartCoord (E := E) j
              (fieldChartRep (I := I) z (gradientField g f hf) y)
            • fderiv ℝ (chartGramOnE (I := I) g z i j) y) y :=
      fun j => (hGdiff i j).hasFDerivAt.mul (hVjdiff j).hasFDerivAt
    have hprod : partialDeriv (E := E) k
        (fun y' => ∑ j, chartGramOnE (I := I) g z i j y'
          * Geodesic.chartCoord (E := E) j
            (fieldChartRep (I := I) z (gradientField g f hf) y')) y
        = ∑ j, (partialDeriv (E := E) k (chartGramOnE (I := I) g z i j) y
              * Geodesic.chartCoord (E := E) j
                (fieldChartRep (I := I) z (gradientField g f hf) y)
            + chartGramOnE (I := I) g z i j y
              * partialDeriv (E := E) k
                (fun y' => Geodesic.chartCoord (E := E) j
                  (fieldChartRep (I := I) z (gradientField g f hf) y')) y) := by
      have hsum := HasFDerivAt.sum (fun j (_ : j ∈ Finset.univ) => hterm j)
      have hfun_eq : (∑ j, fun y' => chartGramOnE (I := I) g z i j y'
            * Geodesic.chartCoord (E := E) j
              (fieldChartRep (I := I) z (gradientField g f hf) y'))
          = fun y' => ∑ j, chartGramOnE (I := I) g z i j y'
            * Geodesic.chartCoord (E := E) j
              (fieldChartRep (I := I) z (gradientField g f hf) y') := by
        funext y'
        simp [Finset.sum_apply]
      rw [hfun_eq] at hsum
      unfold partialDeriv
      rw [hsum.fderiv, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply]
      simp only [smul_eq_mul]
      ring
    -- substitute metric compatibility and the Riesz identity
    have hcompat : ∀ j, partialDeriv (E := E) k (chartGramOnE (I := I) g z i j) y
        = ∑ m, (chartGramOnE (I := I) g z m j y
              * chartChristoffel (I := I) g z k i m y
            + chartGramOnE (I := I) g z i m y
              * chartChristoffel (I := I) g z k j m y) :=
      fun j => partialDeriv_chartGramOnE_eq (I := I) g z i j k y hbase
    have hriesz : ∀ m, ∑ j, chartGramOnE (I := I) g z m j y
          * Geodesic.chartCoord (E := E) j
            (fieldChartRep (I := I) z (gradientField g f hf) y)
        = partialDeriv (E := E) m (f ∘ (extChartAt I z).symm) y :=
      fun m => sum_chartGramOnE_mul_chartCoord_fieldChartRep_gradientField g hf z hy m
    have hexp : ∑ j, (partialDeriv (E := E) k (chartGramOnE (I := I) g z i j) y
          * Geodesic.chartCoord (E := E) j
            (fieldChartRep (I := I) z (gradientField g f hf) y))
        = (∑ m, chartChristoffel (I := I) g z k i m y
            * partialDeriv (E := E) m (f ∘ (extChartAt I z).symm) y)
          + ∑ j, chartGramOnE (I := I) g z i j y
            * (∑ b, chartChristoffel (I := I) g z k b j y
              * Geodesic.chartCoord (E := E) b
                (fieldChartRep (I := I) z (gradientField g f hf) y)) := by
      calc ∑ j, (partialDeriv (E := E) k (chartGramOnE (I := I) g z i j) y
            * Geodesic.chartCoord (E := E) j
              (fieldChartRep (I := I) z (gradientField g f hf) y))
          = ∑ j, ∑ m, (chartGramOnE (I := I) g z m j y
                * chartChristoffel (I := I) g z k i m y
                * Geodesic.chartCoord (E := E) j
                  (fieldChartRep (I := I) z (gradientField g f hf) y)
              + chartGramOnE (I := I) g z i m y
                * chartChristoffel (I := I) g z k j m y
                * Geodesic.chartCoord (E := E) j
                  (fieldChartRep (I := I) z (gradientField g f hf) y)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hcompat j, Finset.sum_mul]
            refine Finset.sum_congr rfl fun m _ => ?_
            ring
        _ = (∑ j, ∑ m, chartGramOnE (I := I) g z m j y
                * chartChristoffel (I := I) g z k i m y
                * Geodesic.chartCoord (E := E) j
                  (fieldChartRep (I := I) z (gradientField g f hf) y))
            + ∑ j, ∑ m, chartGramOnE (I := I) g z i m y
                * chartChristoffel (I := I) g z k j m y
                * Geodesic.chartCoord (E := E) j
                  (fieldChartRep (I := I) z (gradientField g f hf) y) := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun j _ => Finset.sum_add_distrib
        _ = (∑ m, chartChristoffel (I := I) g z k i m y
              * partialDeriv (E := E) m (f ∘ (extChartAt I z).symm) y)
            + ∑ j, chartGramOnE (I := I) g z i j y
              * (∑ b, chartChristoffel (I := I) g z k b j y
                * Geodesic.chartCoord (E := E) b
                  (fieldChartRep (I := I) z (gradientField g f hf) y)) := by
            congr 1
            · rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun m _ => ?_
              rw [← hriesz m, Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
            · rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun m _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
    -- coordinates of the Christoffel contraction against a basis direction
    have hΓcoord : ∀ j : Fin (Module.finrank ℝ E), Geodesic.chartCoord (E := E) j
        (Geodesic.chartChristoffelContraction (I := I) g z ((Module.finBasis ℝ E) k)
          (fieldChartRep (I := I) z (gradientField g f hf) y) y)
        = ∑ b, chartChristoffel (I := I) g z k b j y
            * Geodesic.chartCoord (E := E) b
              (fieldChartRep (I := I) z (gradientField g f hf) y) := by
      intro j
      rw [chartCoord_chartChristoffelContraction]
      calc ∑ a, ∑ b, chartChristoffel (I := I) g z a b j y
            * Geodesic.chartCoord (E := E) a ((Module.finBasis ℝ E) k)
            * Geodesic.chartCoord (E := E) b
              (fieldChartRep (I := I) z (gradientField g f hf) y)
          = ∑ a, (if k = a then (1 : ℝ) else 0)
              * ∑ b, chartChristoffel (I := I) g z a b j y
                * Geodesic.chartCoord (E := E) b
                  (fieldChartRep (I := I) z (gradientField g f hf) y) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [chartCoord_finBasis k a]
            ring
        _ = _ := sum_ite_eq_mul_left k _
    -- assemble: the pairing of the parallel defect with `G_{i·}` vanishes
    have hmain := hdm.symm.trans hprod
    rw [Finset.sum_add_distrib, hexp] at hmain
    calc ∑ j, chartGramOnE (I := I) g z i j y
          * Geodesic.chartCoord (E := E) j
            (fderiv ℝ (fieldChartRep (I := I) z (gradientField g f hf)) y
                ((Module.finBasis ℝ E) k)
              + Geodesic.chartChristoffelContraction (I := I) g z
                  ((Module.finBasis ℝ E) k)
                  (fieldChartRep (I := I) z (gradientField g f hf) y) y)
        = (∑ j, chartGramOnE (I := I) g z i j y
            * partialDeriv (E := E) k
              (fun y' => Geodesic.chartCoord (E := E) j
                (fieldChartRep (I := I) z (gradientField g f hf) y')) y)
          + ∑ j, chartGramOnE (I := I) g z i j y
            * (∑ b, chartChristoffel (I := I) g z k b j y
              * Geodesic.chartCoord (E := E) b
                (fieldChartRep (I := I) z (gradientField g f hf) y)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Geodesic.chartCoord_add, hΓcoord j, mul_add]
          congr 2
          rw [hcoord_fderiv j]
          rfl
      _ = 0 := by linarith [hmain]
  -- Step 2: extend to a general direction by linearity
  set Vy : E := fieldChartRep (I := I) z (gradientField g f hf) y with hVy_def
  have hΓadd : ∀ v₁ v₂ : E,
      Geodesic.chartChristoffelContraction (I := I) g z (v₁ + v₂) Vy y
      = Geodesic.chartChristoffelContraction (I := I) g z v₁ Vy y
        + Geodesic.chartChristoffelContraction (I := I) g z v₂ Vy y := by
    intro v₁ v₂
    rw [Geodesic.chartChristoffelContraction_symm (I := I) g z (v₁ + v₂) Vy y,
      Geodesic.chartChristoffelContraction_add_right,
      ← Geodesic.chartChristoffelContraction_symm (I := I) g z v₁ Vy y,
      ← Geodesic.chartChristoffelContraction_symm (I := I) g z v₂ Vy y]
  have hΓsmul : ∀ (c : ℝ) (v : E),
      Geodesic.chartChristoffelContraction (I := I) g z (c • v) Vy y
      = c • Geodesic.chartChristoffelContraction (I := I) g z v Vy y := by
    intro c v
    rw [Geodesic.chartChristoffelContraction_symm (I := I) g z (c • v) Vy y,
      Geodesic.chartChristoffelContraction_smul_right,
      ← Geodesic.chartChristoffelContraction_symm (I := I) g z v Vy y]
  set ΓL : E →ₗ[ℝ] E :=
    { toFun := fun v => Geodesic.chartChristoffelContraction (I := I) g z v Vy y
      map_add' := hΓadd
      map_smul' := hΓsmul } with hΓL_def
  have hΓw : Geodesic.chartChristoffelContraction (I := I) g z w Vy y
      = ∑ a, (Module.finBasis ℝ E).repr w a
          • Geodesic.chartChristoffelContraction (I := I) g z
              ((Module.finBasis ℝ E) a) Vy y := by
    have h1 : Geodesic.chartChristoffelContraction (I := I) g z w Vy y = ΓL w := rfl
    rw [h1]
    conv_lhs => rw [← (Module.finBasis ℝ E).sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul]
    rfl
  conv_lhs => rw [← (Module.finBasis ℝ E).sum_repr w]
  rw [map_sum, hΓw, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, ← smul_neg]
  congr 1
  exact eq_neg_of_add_eq_zero_left (hbasisdir a)

/-! ### Variational solutions along parallel-field flow lines -/

/-- **Math.** Along a chart flow line `u' = W(u)` of a field `W` satisfying
the parallel identity `∂W(y)·w = −Γ(w, W(y))(y)`, any solution `d` of the
**variational equation** `d' = ∂W(u(t))·d` is a parallel coordinate field:
`Dd/dt = d' + Γ(u', d)(u) = 0`. Blueprint `lem:parallel-gradient-flow`(4),
linearized form; instantiated by the gradient field of a Busemann-type
function (`fderiv_fieldChartRep_gradientField_of_bochner`) and its negation. -/
theorem covariantDerivCoord_variational_eq_zero
    (g : RiemannianMetric I M) (z : M) {W : E → E}
    (hpar : ∀ y ∈ (extChartAt I z).target, ∀ w : E,
      fderiv ℝ W y w = - Geodesic.chartChristoffelContraction (I := I) g z w (W y) y)
    {u d : ℝ → E} {t : ℝ}
    (hmem : u t ∈ (extChartAt I z).target)
    (hu : HasDerivAt u (W (u t)) t)
    (hd : HasDerivAt d (fderiv ℝ W (u t) (d t)) t) :
    covariantDerivCoord (I := I) g z u d t = 0 := by
  rw [covariantDerivCoord_def, hu.deriv, hd.deriv, hpar (u t) hmem (d t),
    Geodesic.chartChristoffelContraction_symm]
  exact neg_add_cancel _

/-- **Math.** **Constancy of the chart Gram inner product along variational
solutions** (blueprint `lem:parallel-gradient-flow`(4), chart-level heart):
if `u` solves `u' = W(u)` for a field `W` satisfying the parallel identity
`∂W = −Γ(·, W)` on the chart target, and `d₁, d₂` solve the variational
equation `d' = ∂W(u)·d` on `[a, b]`, all staying in the chart target, then
`⟨d₁(t), d₂(t)⟩_{G(u(t))}` is constant on `[a, b]`. -/
theorem chartMetricInner_variational_eq_left
    (g : RiemannianMetric I M) (z : M) {W : E → E}
    (hpar : ∀ y ∈ (extChartAt I z).target, ∀ w : E,
      fderiv ℝ W y w = - Geodesic.chartChristoffelContraction (I := I) g z w (W y) y)
    {u d₁ d₂ : ℝ → E} {a b : ℝ}
    (hmem : ∀ t ∈ Icc a b, u t ∈ (extChartAt I z).target)
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (W (u t)) t)
    (hd₁ : ∀ t ∈ Icc a b, HasDerivAt d₁ (fderiv ℝ W (u t) (d₁ t)) t)
    (hd₂ : ∀ t ∈ Icc a b, HasDerivAt d₂ (fderiv ℝ W (u t) (d₂ t)) t)
    {t : ℝ} (ht : t ∈ Icc a b) :
    chartMetricInner (I := I) g z (u t) (d₁ t) (d₂ t)
      = chartMetricInner (I := I) g z (u a) (d₁ a) (d₂ a) := by
  have hopen : IsOpen (extChartAt I z).target := isOpen_extChartAt_target (I := I) z
  -- the inner product has vanishing derivative at every point of `[a, b]`
  have hderiv : ∀ s ∈ Icc a b, HasDerivAt
      (fun r => chartMetricInner (I := I) g z (u r) (d₁ r) (d₂ r)) 0 s := by
    intro s hs
    have hbase : (extChartAt I z).symm (u s)
        ∈ (trivializationAt E (TangentSpace I) z).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source, ← extChartAt_source (I := I)]
      exact (extChartAt I z).map_target (hmem s hs)
    have hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g z i j) (u s) :=
      fun i j => ((chartGramOnE_contDiffOn (I := I) g z i j).contDiffAt
        (hopen.mem_nhds (hmem s hs))).differentiableAt (by simp)
    have h := hasDerivAt_chartMetricInner_along (I := I) g z u d₁ d₂
      (hu s hs).differentiableAt (hd₁ s hs).differentiableAt
      (hd₂ s hs).differentiableAt hG hbase
    have hz₁ : covariantDerivCoord (I := I) g z u d₁ s = 0 :=
      covariantDerivCoord_variational_eq_zero g z hpar (hmem s hs) (hu s hs)
        (hd₁ s hs)
    have hz₂ : covariantDerivCoord (I := I) g z u d₂ s = 0 :=
      covariantDerivCoord_variational_eq_zero g z hpar (hmem s hs) (hu s hs)
        (hd₂ s hs)
    rw [hz₁, hz₂] at h
    have hzero : chartMetricInner (I := I) g z (u s) 0 (d₂ s)
        + chartMetricInner (I := I) g z (u s) (d₁ s) 0 = 0 := by
      have hc0 : ∀ j : Fin (Module.finrank ℝ E),
          Geodesic.chartCoord (E := E) j (0 : E) = 0 := by
        intro j
        rw [Geodesic.chartCoord_def]
        simp
      simp only [chartMetricInner_def, hc0, mul_zero, zero_mul,
        Finset.sum_const_zero, add_zero]
    rwa [hzero] at h
  -- continuity on `[a, b]`, and constancy from the vanishing derivative
  have hcont : ContinuousOn
      (fun r => chartMetricInner (I := I) g z (u r) (d₁ r) (d₂ r)) (Icc a b) :=
    fun s hs => ((hderiv s hs).continuousAt).continuousWithinAt
  exact constant_of_has_deriv_right_zero hcont
    (fun s hs => ((hderiv s (mem_Icc_of_Ico hs)).hasDerivWithinAt)) t ht

end MorganTianLib

end
