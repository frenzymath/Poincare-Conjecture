import MorganTianLib.Ch01.CurvatureFrameBridge
import MorganTianLib.Ch01.FrameReduction

/-!
# Poincaré Ch. 1 — the curvature bridge and the sectional-curvature bound

The two headline results built from the infrastructure of
`MorganTianLib.Ch01.CurvatureFrameBridge`:

* `curvatureFormAt_chartFrame` — **the manifold ↔ chart curvature bridge**:
  for `p` in the chart at `α` with `y = φ(p)` and `v w z t : E`,
  `ℛ(F v, F w, F z, F t)(p) = −⟨chartCurvature g α y v w z, t⟩_{G(y)}`,
  where `F` realizes coordinates on the chart frame; the sign is the
  Morgan–Tian ↔ do Carmo convention flip;
* `chartCurvature_pairing_le_of_sectionalCurvatureAt_le` (and its product
  form) — **sectional bound ⇒ Jacobi-operator bound**: `K(P) ≤ K` at the
  point under `y` gives `⟨ℛ(J,u)u, J⟩_y ≤ K(⟨J,J⟩⟨u,u⟩ − ⟨J,u⟩²)` in the
  chart Gram inner product — the curvature hypothesis `hcurv` of
  `MorganTianLib.jacobi_frame_sturm_comparison`
  (blueprint `lem:jacobi-frame-reduction`, feeding `lem:conjugate-sturm`).

Blueprint: `lem:chart-curvature-coordinates`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.2.
-/

open Set Filter Riemannian Riemannian.Tensor
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### The bridge: pointwise curvature tensor = chart curvature -/

set_option maxHeartbeats 1600000 in
/-- **Math.** **The manifold ↔ chart curvature bridge.** For `p` in the chart
at `α` with chart image `y = φ(p)` and any coordinate vectors
`v, w, z, t : E`, the pointwise curvature `(0,4)`-tensor of the Levi-Civita
connection evaluated on the chart-frame realizations
`F(x) = ∑_a x^a X_a(p)` is the chart Gram pairing of the Christoffel-formula
curvature:
`ℛ(F v, F w, F z, F t)(p) = −⟨ℛ_chart(y)(v, w)z, t⟩_{G(y)}`.
The sign is the do Carmo ↔ Morgan–Tian convention flip recorded in
`MorganTianLib.Ch01.PointwiseCurvature`; `chartCurvature` is Morgan–Tian's
`∇_X∇_Y − ∇_Y∇_X` on commuting fields while `curvatureForm` is built from do
Carmo's `R(X,Y) = ∇_Y∇_X − ∇_X∇_Y + ∇_{[X,Y]}`.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem curvatureFormAt_chartFrame [I.Boundaryless]
    (g : RiemannianMetric I M) {α p : M} (hp : p ∈ (chartAt H α).source)
    (v w z t : E) :
    curvatureFormAt g g.leviCivitaConnection p
        (∑ a, Geodesic.chartCoord (E := E) a v • chartBasisVecFiber (I := I) α a p)
        (∑ b, Geodesic.chartCoord (E := E) b w • chartBasisVecFiber (I := I) α b p)
        (∑ c, Geodesic.chartCoord (E := E) c z • chartBasisVecFiber (I := I) α c p)
        (∑ d, Geodesic.chartCoord (E := E) d t • chartBasisVecFiber (I := I) α d p)
      = - chartMetricInner (I := I) g α (extChartAt I α p)
          (chartCurvature (I := I) g α (extChartAt I α p) v w z) t := by
  classical
  have hy_mem : (extChartAt I α p) ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (by rwa [extChartAt_source])
  have hy_int : (extChartAt I α p) ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy_mem
  have hpe : (extChartAt I α).symm (extChartAt I α p) = p :=
    (extChartAt I α).left_inv (by rwa [extChartAt_source])
  -- the chart frame with its neighbourhood Christoffel formula
  obtain ⟨Z, U, hUopen, hpU, hUsub, hframe, hchristoffel⟩ :=
    exists_chartFrame_leviCivita_christoffel_nhds (I := I) g hp
  -- globally smooth extensions of the pulled-back Christoffel symbols
  have hsmooth : ∀ a b m, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun q => chartChristoffel (I := I) g α a b m (extChartAt I α q))
      (chartAt H α).source := by
    intro a b m
    have h1 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chartChristoffel (I := I) g α a b m)
        (interior (extChartAt I α).target) :=
      (chartChristoffel_contDiffOn_interior (I := I) g α a b m).contMDiffOn
    have h2 : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
      contMDiffOn_extChartAt
    exact h1.comp h2 fun q hq => by
      rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
      exact (extChartAt I α).map_source (by rwa [extChartAt_source])
  have hext : ∀ a b m, ∃ F : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ F ∧
      ∀ᶠ q in 𝓝 p, F q = chartChristoffel (I := I) g α a b m (extChartAt I α q) :=
    fun a b m => exists_contMDiff_eventuallyEq (chartAt H α).open_source
      (hsmooth a b m) hp
  choose F hFsmooth hFeq using hext
  have hγdiffAt : ∀ a b m,
      DifferentiableAt ℝ (chartChristoffel (I := I) g α a b m) (extChartAt I α p) := fun a b m =>
    (((chartChristoffel_contDiffOn_interior (I := I) g α a b m).contDiffAt
      (isOpen_interior.mem_nhds hy_int)).differentiableAt (by norm_num))
  -- the covariant derivative field in local form
  have hcovloc : ∀ a b, (g.leviCivitaConnection.cov (Z a) (Z b))
      =ᶠ[𝓝 p] fun q => ∑ m, F a b m q • Z m q := by
    intro a b
    have hU : ∀ᶠ q in 𝓝 p, q ∈ U := hUopen.mem_nhds hpU
    have hFs : ∀ᶠ q in 𝓝 p, ∀ m, F a b m q
        = chartChristoffel (I := I) g α a b m (extChartAt I α q) :=
      (Filter.eventually_all).mpr fun m => hFeq a b m
    filter_upwards [hU, hFs] with q hqU hFq
    rw [hchristoffel a b q hqU]
    exact (Finset.sum_congr rfl fun m _ => by rw [hFq m]).symm
  -- directional derivatives of the extended symbols along the frame
  have hdirF : ∀ a b m c, (Z c).dir (F a b m) p
      = partialDeriv (E := E) c (chartChristoffel (I := I) g α a b m) (extChartAt I α p) := by
    intro a b m c
    show mfderiv I 𝓘(ℝ, ℝ) (F a b m) p (Z c p) = _
    rw [Filter.EventuallyEq.mfderiv_eq (hFeq a b m), hframe c p hpU]
    exact mfderiv_comp_extChartAt_chartBasisVecFiber (I := I) hp (hγdiffAt a b m) c
  have hFp : ∀ a b m, F a b m p = chartChristoffel (I := I) g α a b m (extChartAt I α p) :=
    fun a b m => Filter.EventuallyEq.eq_of_nhds (hFeq a b m)
  -- the double covariant derivative on the frame, in components
  have hcovcov : ∀ a b c, (g.leviCivitaConnection.cov (Z c) (g.leviCivitaConnection.cov (Z a) (Z b))) p
      = ∑ m, (partialDeriv (E := E) c (chartChristoffel (I := I) g α a b m) (extChartAt I α p)
            • Z m p
          + chartChristoffel (I := I) g α a b m (extChartAt I α p)
            • ∑ r, chartChristoffel (I := I) g α c m r (extChartAt I α p) • Z r p) := by
    intro a b c
    rw [cov_apply_of_eventuallyEq_sum_smul g.leviCivitaConnection (Z c) Finset.univ
      (hFsmooth a b) Z (hcovloc a b)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hdirF a b m c, hFp a b m, hchristoffel c m p hpU]
  -- the bracket term vanishes on the commuting chart frame
  have hgerm : ∀ a, (fun q => Z a q)
      =ᶠ[𝓝 p] (fun q => chartBasisVecFiber (I := I) α a q) :=
    fun a => eventually_of_mem (hUopen.mem_nhds hpU) (fun r hr => hframe a r hr)
  have hbracket : ∀ a b c, (g.leviCivitaConnection.cov (bracketField (Z a) (Z b)) (Z c)) p = 0 := by
    intro a b c
    have hbr0 : bracketField (Z a) (Z b) p = (0 : SmoothVectorField I M) p := by
      show DCLieBracket (Z a) (Z b) p = _
      have : DCLieBracket (Z a) (Z b) p = 0 := by
        show VectorField.mlieBracket I (Z a).toFun (Z b).toFun p = 0
        rw [Filter.EventuallyEq.mlieBracket_vectorField_eq (hgerm a) (hgerm b)]
        exact mlieBracket_chartBasisVecFiber_eq_zero (I := I) α a b hp
      rw [this, SmoothVectorField.zero_apply]
    rw [g.leviCivitaConnection.cov_congr_apply_left (Z c) hbr0, g.leviCivitaConnection.cov_zero_left]
  -- the Gram entries of the frame
  have hgram : ∀ m l, g.metricInner p (Z m p) (Z l p)
      = chartGramOnE (I := I) g α m l (extChartAt I α p) := by
    intro m l
    rw [hframe m p hpU, hframe l p hpU, chartGramOnE, hpe]
    rfl
  -- the frame identity, per basis 4-tuple
  have hframe_form : ∀ i j k l : Fin (Module.finrank ℝ E),
      curvatureFormAt g g.leviCivitaConnection p
          (chartBasisVecFiber (I := I) α i p) (chartBasisVecFiber (I := I) α j p)
          (chartBasisVecFiber (I := I) α k p) (chartBasisVecFiber (I := I) α l p)
        = - chartMetricInner (I := I) g α (extChartAt I α p)
            (chartCurvature (I := I) g α (extChartAt I α p) (Module.finBasis ℝ E i)
              (Module.finBasis ℝ E j) (Module.finBasis ℝ E k))
            (Module.finBasis ℝ E l) := by
    intro i j k l
    have h1 : curvatureFormAt g g.leviCivitaConnection p
        (chartBasisVecFiber (I := I) α i p) (chartBasisVecFiber (I := I) α j p)
        (chartBasisVecFiber (I := I) α k p) (chartBasisVecFiber (I := I) α l p)
        = g.leviCivitaConnection.curvatureForm g (Z i) (Z j) (Z k) (Z l) p := by
      rw [← hframe i p hpU, ← hframe j p hpU, ← hframe k p hpU, ← hframe l p hpU]
      exact curvatureFormAt_eq g g.leviCivitaConnection (Z i) (Z j) (Z k) (Z l) p
    rw [h1]
    show g.metricInner p ((g.leviCivitaConnection.curvature (Z i) (Z j) (Z k)) p) (Z l p) = _
    rw [g.leviCivitaConnection.curvature_apply, hbracket i j k, add_zero, sub_eq_add_neg,
      g.metricInner_add_left, g.metricInner_neg_left, hcovcov i k j, hcovcov j k i]
    -- expand the two pairings into Christoffel/Gram sums
    have hpair : ∀ a b c,
        g.metricInner p
          (∑ m, (partialDeriv (E := E) c (chartChristoffel (I := I) g α a b m) (extChartAt I α p)
              • Z m p
            + chartChristoffel (I := I) g α a b m (extChartAt I α p)
              • ∑ r, chartChristoffel (I := I) g α c m r (extChartAt I α p) • Z r p)) (Z l p)
        = (∑ m, partialDeriv (E := E) c (chartChristoffel (I := I) g α a b m) (extChartAt I α p)
              * chartGramOnE (I := I) g α m l (extChartAt I α p))
          + ∑ m, chartChristoffel (I := I) g α a b m (extChartAt I α p)
              * ∑ r, chartChristoffel (I := I) g α c m r (extChartAt I α p)
                  * chartGramOnE (I := I) g α r l (extChartAt I α p) := by
      intro a b c
      rw [Finset.sum_add_distrib, g.metricInner_add_left,
        metricInner_sum_smul_left, metricInner_sum_smul_left]
      congr 1
      · exact Finset.sum_congr rfl fun m _ => by rw [hgram m l]
      · refine Finset.sum_congr rfl fun m _ => ?_
        rw [metricInner_sum_smul_left]
        congr 1
        exact Finset.sum_congr rfl fun r _ => by rw [hgram r l]
    rw [hpair i k j, hpair j k i]
    -- expand the chart-curvature side
    rw [chartCurvature_basis (I := I) g α hy_int i j k, chartMetricInner_sum_left]
    have hterm : ∀ m, chartMetricInner (I := I) g α (extChartAt I α p)
        ((partialDeriv (E := E) i (chartChristoffel (I := I) g α j k m) (extChartAt I α p)
            - partialDeriv (E := E) j (chartChristoffel (I := I) g α i k m) (extChartAt I α p)
            + ∑ r, (chartChristoffel (I := I) g α j k r (extChartAt I α p)
                      * chartChristoffel (I := I) g α i r m (extChartAt I α p)
                  - chartChristoffel (I := I) g α i k r (extChartAt I α p)
                      * chartChristoffel (I := I) g α j r m (extChartAt I α p)))
          • Module.finBasis ℝ E m) (Module.finBasis ℝ E l)
        = (partialDeriv (E := E) i (chartChristoffel (I := I) g α j k m) (extChartAt I α p)
            - partialDeriv (E := E) j (chartChristoffel (I := I) g α i k m) (extChartAt I α p)
            + ∑ r, (chartChristoffel (I := I) g α j k r (extChartAt I α p)
                      * chartChristoffel (I := I) g α i r m (extChartAt I α p)
                  - chartChristoffel (I := I) g α i k r (extChartAt I α p)
                      * chartChristoffel (I := I) g α j r m (extChartAt I α p)))
          * chartGramOnE (I := I) g α m l (extChartAt I α p) := by
      intro m
      rw [chartMetricInner_smul_left, chartMetricInner_basis]
    simp only [hterm]
    -- reduce to a scalar sum identity
    have hswap : ∀ (A B : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
        (C : Fin (Module.finrank ℝ E) → ℝ),
        (∑ m, C m * ∑ r, A m r * chartGramOnE (I := I) g α r l (extChartAt I α p))
        = ∑ m, (∑ r, C r * A r m) * chartGramOnE (I := I) g α m l (extChartAt I α p) := by
      intro A B C
      calc (∑ m, C m * ∑ r, A m r * chartGramOnE (I := I) g α r l (extChartAt I α p))
          = ∑ m, ∑ r, C m * A m r * chartGramOnE (I := I) g α r l (extChartAt I α p) := by
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun r _ => by ring
        _ = ∑ r, ∑ m, C m * A m r * chartGramOnE (I := I) g α r l (extChartAt I α p) :=
            Finset.sum_comm
        _ = ∑ m, (∑ r, C r * A r m) * chartGramOnE (I := I) g α m l (extChartAt I α p) := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [Finset.sum_mul]
    rw [hswap (fun m r => chartChristoffel (I := I) g α j m r (extChartAt I α p))
        (fun _ _ => 0) (fun m => chartChristoffel (I := I) g α i k m (extChartAt I α p)),
      hswap (fun m r => chartChristoffel (I := I) g α i m r (extChartAt I α p))
        (fun _ _ => 0) (fun m => chartChristoffel (I := I) g α j k m (extChartAt I α p))]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_sub_distrib]
    ring
  -- quadrilinear expansion on both sides
  rw [curvatureFormAt_sum₄]
  conv_rhs =>
    rw [show v = ∑ a, Geodesic.chartCoord (E := E) a v • Module.finBasis ℝ E a from
        by simp [Geodesic.chartCoord_def, Module.Basis.sum_repr],
      show w = ∑ b, Geodesic.chartCoord (E := E) b w • Module.finBasis ℝ E b from
        by simp [Geodesic.chartCoord_def, Module.Basis.sum_repr],
      show z = ∑ c, Geodesic.chartCoord (E := E) c z • Module.finBasis ℝ E c from
        by simp [Geodesic.chartCoord_def, Module.Basis.sum_repr],
      show t = ∑ d, Geodesic.chartCoord (E := E) d t • Module.finBasis ℝ E d from
        by simp [Geodesic.chartCoord_def, Module.Basis.sum_repr]]
  rw [chartCurvature_sum₃ (I := I) g α (extChartAt I α p) Finset.univ]
  rw [chartMetricInner_sum_left, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [chartMetricInner_sum_left, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [chartMetricInner_sum_left, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [chartMetricInner_sum_right, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [chartMetricInner_smul_left, chartMetricInner_smul_right, hframe_form a b c d]
  ring

/-! ### From a sectional-curvature bound to the chart curvature bound -/

/-- **Math.** An algebraic curvature form with all sectional curvatures `≤ K`
satisfies `B(x,y,x,y) ≤ K·(|x|²|y|² − ⟨x,y⟩²)`: clear the denominator when
`x, y` span a plane; both sides vanish when they are dependent.
Blueprint: `lem:chart-curvature-coordinates` / `def:sectional-curvature`. -/
theorem alg_curvature_le_of_sectionalCurvature_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B) {K : ℝ}
    (hK : ∀ x y : V, Riemannian.sectionalCurvature B x y ≤ K) (x y : V) :
    B x y x y ≤ K * wedgeSq x y := by
  by_cases hli : LinearIndependent ℝ ![x, y]
  · have hw : 0 < wedgeSq x y := (wedgeSq_pos_iff_linearIndependent x y).mpr hli
    have h : B x y x y / wedgeSq x y ≤ K := hK x y
    calc B x y x y = B x y x y / wedgeSq x y * wedgeSq x y := by
          field_simp
      _ ≤ K * wedgeSq x y := mul_le_mul_of_nonneg_right h hw.le
  · have hw0 : wedgeSq x y = 0 := by
      rcases lt_or_eq_of_le (wedgeSq_nonneg x y) with hlt | heq
      · exact absurd ((wedgeSq_pos_iff_linearIndependent x y).mp hlt) hli
      · exact heq.symm
    have hB0 : B x y x y = 0 := by
      rw [linearIndependent_fin2] at hli
      push_neg at hli
      simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at hli
      by_cases hy0 : y = 0
      · subst hy0
        have h1 : B x 0 x 0 = -B 0 x x 0 := hB.antisymm₁₂ x 0 x 0
        have h2 : B 0 x x 0 = 0 := by
          have h3 := hB.smul_left 0 (0 : V) x x 0
          simpa using h3
        rw [h1, h2, neg_zero]
      · obtain ⟨a, hxa⟩ := hli hy0
        subst hxa
        have hyy : B y y (a • y) y = 0 := by
          have h4 := hB.antisymm₁₂ y y (a • y) y
          linarith
        have h5 := hB.smul_left a y y (a • y) y
        rw [h5, hyy, mul_zero]
    rw [hw0, hB0, mul_zero]

set_option maxHeartbeats 1600000 in
/-- **Math.** **Sectional-curvature bound ⇒ chart Jacobi-operator bound.**
If every sectional curvature at the manifold point under the chart point `y`
is `≤ K`, the chart curvature satisfies, in the chart Gram inner product,
`⟨ℛ(J, u)u, J⟩_y ≤ K(⟨J,J⟩⟨u,u⟩ − ⟨J,u⟩²)` for all coordinate vectors
`J, u : E`. Combined with `MorganTianLib.jacobi_frame_sturm_comparison`
(blueprint `lem:jacobi-frame-reduction`) this turns Morgan–Tian's hypothesis
`K(P) ≤ K` into the Sturm-comparison hypothesis on the Jacobi ODE.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem chartCurvature_pairing_le_of_sectionalCurvatureAt_le [I.Boundaryless]
    (g : RiemannianMetric I M) {α : M} {y : E} {K : ℝ}
    (hy : y ∈ (extChartAt I α).target)
    (hsec : ∀ v w : TangentSpace I ((extChartAt I α).symm y),
      sectionalCurvatureAt g g.leviCivitaConnection
        ((extChartAt I α).symm y) v w ≤ K)
    (J u : E) :
    chartMetricInner (I := I) g α y (chartCurvature (I := I) g α y J u u) J
      ≤ K * (chartMetricInner (I := I) g α y J J
            * chartMetricInner (I := I) g α y u u
          - chartMetricInner (I := I) g α y J u
            * chartMetricInner (I := I) g α y J u) := by
  classical
  set p := (extChartAt I α).symm y with hp_def
  have hp : p ∈ (chartAt H α).source := by
    have h := (extChartAt I α).map_target hy
    rwa [extChartAt_source] at h
  have hyp : extChartAt I α p = y := (extChartAt I α).right_inv hy
  set nabla := g.leviCivitaConnection with hnabla
  have hLC : nabla.IsLeviCivita g :=
    nabla.isLeviCivita_of_koszulDual g
      (fun X Y W r => g.koszulDualSection_dual X Y W r)
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hB : IsAlgCurvatureForm (curvatureFormAt g nabla p) :=
    isAlgCurvatureForm_curvatureFormAt g nabla hLC p
  set FJ : TangentSpace I p :=
    ∑ a, Geodesic.chartCoord (E := E) a J • chartBasisVecFiber (I := I) α a p
    with hFJ
  set Fu : TangentSpace I p :=
    ∑ a, Geodesic.chartCoord (E := E) a u • chartBasisVecFiber (I := I) α a p
    with hFu
  have hbridge : curvatureFormAt g nabla p FJ Fu Fu FJ
      = - chartMetricInner (I := I) g α y
          (chartCurvature (I := I) g α y J u u) J := by
    have h := curvatureFormAt_chartFrame (I := I) g hp J u u J
    rwa [hyp] at h
  have hpair : chartMetricInner (I := I) g α y
        (chartCurvature (I := I) g α y J u u) J
      = curvatureFormAt g nabla p FJ Fu FJ Fu := by
    have h2 : curvatureFormAt g nabla p FJ Fu FJ Fu
        = - curvatureFormAt g nabla p FJ Fu Fu FJ := hB.antisymm₃₄ FJ Fu FJ Fu
    rw [h2, hbridge, neg_neg]
  have hle : curvatureFormAt g nabla p FJ Fu FJ Fu ≤ K * wedgeSq FJ Fu :=
    alg_curvature_le_of_sectionalCurvature_le hB (fun v w => hsec v w) FJ Fu
  have hwedge : wedgeSq FJ Fu
      = chartMetricInner (I := I) g α y J J * chartMetricInner (I := I) g α y u u
        - chartMetricInner (I := I) g α y J u
          * chartMetricInner (I := I) g α y J u := by
    have hJJ : (inner ℝ FJ FJ : ℝ) = chartMetricInner (I := I) g α y J J := by
      show g.metricInner p FJ FJ = _
      rw [hFJ]
      have h := metricInner_chartFrame (I := I) g hp J J
      rwa [hyp] at h
    have huu : (inner ℝ Fu Fu : ℝ) = chartMetricInner (I := I) g α y u u := by
      show g.metricInner p Fu Fu = _
      rw [hFu]
      have h := metricInner_chartFrame (I := I) g hp u u
      rwa [hyp] at h
    have hJu : (inner ℝ FJ Fu : ℝ) = chartMetricInner (I := I) g α y J u := by
      show g.metricInner p FJ Fu = _
      rw [hFJ, hFu]
      have h := metricInner_chartFrame (I := I) g hp J u
      rwa [hyp] at h
    rw [wedgeSq, hJJ, huu, hJu]
  rw [hpair, ← hwedge]
  exact hle

/-- **Math.** Product form of
`chartCurvature_pairing_le_of_sectionalCurvatureAt_le` for `K ≥ 0`:
`⟨ℛ(J, u)u, J⟩_y ≤ K ⟨J,J⟩⟨u,u⟩` — with `|u| = 1` along a unit-speed geodesic
this is precisely the `hcurv` hypothesis of
`MorganTianLib.jacobi_frame_sturm_comparison`.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem chartCurvature_pairing_le_of_sectionalCurvatureAt_le' [I.Boundaryless]
    (g : RiemannianMetric I M) {α : M} {y : E} {K : ℝ} (hK : 0 ≤ K)
    (hy : y ∈ (extChartAt I α).target)
    (hsec : ∀ v w : TangentSpace I ((extChartAt I α).symm y),
      sectionalCurvatureAt g g.leviCivitaConnection
        ((extChartAt I α).symm y) v w ≤ K)
    (J u : E) :
    chartMetricInner (I := I) g α y (chartCurvature (I := I) g α y J u u) J
      ≤ K * (chartMetricInner (I := I) g α y J J
            * chartMetricInner (I := I) g α y u u) := by
  refine (chartCurvature_pairing_le_of_sectionalCurvatureAt_le (I := I) g hy hsec
    J u).trans ?_
  have h := mul_self_nonneg (chartMetricInner (I := I) g α y J u)
  nlinarith

end MorganTianLib

end
