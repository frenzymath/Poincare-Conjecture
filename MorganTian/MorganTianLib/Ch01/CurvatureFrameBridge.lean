import MorganTianLib.Ch01.ChartCurvature
import MorganTianLib.Ch01.JacobiField
import MorganTianLib.Ch01.PointwiseCurvature
import OpenGALib.Riemannian.Connection.ChristoffelBridge
import OpenGALib.Riemannian.Connection.ChartFrameBridge
import OpenGALib.Riemannian.Geodesic.CovariantDerivative

/-!
# Poincaré Ch. 1 — the manifold ↔ chart curvature bridge

This file identifies the **chart-level curvature** `chartCurvature g α y`
(defined from the Christoffel symbols in the chart at `α`,
`MorganTianLib.Ch01.ChartCurvature`) with the **manifold-level pointwise
curvature tensor** `curvatureFormAt g ∇ p` (defined from the Levi-Civita
connection on vector fields, `MorganTianLib.Ch01.PointwiseCurvature`), and
derives the consequence the comparison-geometry pipeline consumes: a bound
`K(P) ≤ K` on the sectional curvatures at a point yields the quadratic-form
bound `⟨ℛ(J, u)u, J⟩_y ≤ K‖J‖²‖u‖²` on the chart curvature in the chart Gram
inner product — the hypothesis `hcurv` of
`MorganTianLib.jacobi_frame_sturm_comparison`.

* `exists_contMDiff_eventuallyEq` — a smooth scalar function defined on an
  open set extends to a globally smooth function agreeing near a point
  (scalar analogue of `Riemannian.exists_smoothVectorField_eventuallyEq`);
* `cov_congr_apply_right` — `(∇_X Y)(p)` only depends on the germ of `Y`
  at `p`;
* `exists_chartFrame_leviCivita_christoffel_nhds` — the chart-frame
  Christoffel formula `∇_{X_i} X_j = ∑_m Γ^m_{ij} X_m` on a **neighbourhood**
  of a chart point (the pointwise version is OpenGALib's
  `Riemannian.exists_chartFrame_leviCivita_christoffel`);
* `curvatureFormAt_chartFrame` — **the bridge**: for `p` in the chart at `α`
  with `y = φ(p)` and any `v w z t : E`,
  `ℛ(F v, F w, F z, F t)(p) = −⟨chartCurvature g α y v w z, t⟩_{G(y)}`,
  where `F` realizes a coordinate vector on the chart frame and `⟨·,·⟩_G` is
  the chart Gram pairing `chartMetricInner`. The sign is the Morgan–Tian ↔
  do Carmo convention flip already recorded in
  `MorganTianLib.Ch01.PointwiseCurvature`;
* `chartCurvature_pairing_le_of_sectionalCurvatureAt_le` — the **payoff**:
  `K(P) ≤ K` for all tangent 2-planes at `p` implies
  `⟨ℛ(J, u)u, J⟩_y ≤ K(⟨J,J⟩⟨u,u⟩ − ⟨J,u⟩²) ≤ K⟨J,J⟩⟨u,u⟩` in the chart
  Gram inner product at `y = φ(p)` — the exact curvature hypothesis of the
  frame reduction `MorganTianLib.jacobi_frame_sturm_comparison`
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

/-! ### A globally smooth extension of a locally defined smooth scalar -/

/-- **Math.** A smooth scalar function defined on an open set `s ⊆ M` admits a
globally smooth extension agreeing with it near any `x ∈ s` — the scalar
analogue of `Riemannian.exists_smoothVectorField_eventuallyEq`, by the same
convex-selection argument.
Blueprint: `lem:chart-curvature-coordinates` (locality infrastructure). -/
theorem exists_contMDiff_eventuallyEq [SigmaCompactSpace M] [T2Space M]
    {f : M → ℝ} {s : Set M} (hs : IsOpen s)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f s) {x : M} (hx : x ∈ s) :
    ∃ F : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ F ∧ ∀ᶠ y in 𝓝 x, F y = f y := by
  classical
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨K, hK_nhds, hK_closed, hK_sub⟩ :=
    exists_mem_nhds_isClosed_subset (hs.mem_nhds hx)
  set V : Set M := interior K with hV
  have hxV : x ∈ V := mem_interior_iff_mem_nhds.mpr hK_nhds
  have hV_open : IsOpen V := isOpen_interior
  have hclV_sub : closure V ⊆ s :=
    (hK_closed.closure_subset_iff.mpr interior_subset).trans hK_sub
  set t : M → Set ℝ := fun q => if q ∈ V then {f q} else Set.univ with ht
  have hconv : ∀ q, Convex ℝ (t q) := by
    intro q
    by_cases h : q ∈ V
    · simp only [ht, if_pos h]; exact convex_singleton (f q)
    · simp only [ht, if_neg h]; exact convex_univ
  have hlocal : ∀ x₀ : M, ∃ U ∈ 𝓝 x₀, ∃ gloc : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ gloc U ∧ ∀ y ∈ U, gloc y ∈ t y := by
    intro x₀
    by_cases hx0 : x₀ ∈ closure V
    · refine ⟨s, hs.mem_nhds (hclV_sub hx0), f, hf, ?_⟩
      intro y _
      by_cases hyV : y ∈ V
      · simp only [ht, if_pos hyV, Set.mem_singleton_iff]
      · simp only [ht, if_neg hyV]; exact Set.mem_univ _
    · refine ⟨(closure V)ᶜ, (isClosed_closure.isOpen_compl).mem_nhds hx0,
        fun _ => 0, contMDiffOn_const, ?_⟩
      intro y hy
      have hyV : y ∉ V := fun h => hy (subset_closure h)
      simp only [ht, if_neg hyV]; exact Set.mem_univ _
  obtain ⟨F, hF⟩ :=
    exists_contMDiffMap_forall_mem_convex_of_local (I := I) (n := (⊤ : ℕ∞)) hconv hlocal
  refine ⟨F, F.contMDiff, ?_⟩
  filter_upwards [hV_open.mem_nhds hxV] with y hy
  have hFy := hF y
  simpa only [ht, if_pos hy, Set.mem_singleton_iff] using hFy

/-! ### Germ locality of the covariant derivative in its second slot -/

/-- **Math.** `∇_X τ` vanishes at `p` when `τ` vanishes near `p`: write
`τ = f·τ` with `f(p) = 0` (`exists_smul_eq_self_of_eventuallyEq_zero`) and
apply the Leibniz rule.
Blueprint: `lem:chart-curvature-coordinates` (locality infrastructure). -/
theorem cov_apply_eq_zero_of_eventuallyEq_zero_right [SigmaCompactSpace M] [T2Space M]
    (nabla : AffineConnection I M) (X : SmoothVectorField I M)
    {τ : SmoothVectorField I M} {p : M} (hτ : ∀ᶠ q in 𝓝 p, τ q = 0) :
    nabla.cov X τ p = 0 := by
  obtain ⟨f, hf, hfp, hfτ⟩ := exists_smul_eq_self_of_eventuallyEq_zero hτ
  have h := nabla.leibniz f hf X τ p
  rw [hfτ, hτ.self_of_nhds, smul_zero, add_zero, hfp, zero_smul] at h
  exact h

/-- **Math.** **Germ locality of `∇` in the differentiated slot**: if
`Y = Y'` near `p` then `(∇_X Y)(p) = (∇_X Y')(p)`.
Blueprint: `lem:chart-curvature-coordinates` (locality infrastructure). -/
theorem cov_congr_apply_right [SigmaCompactSpace M] [T2Space M]
    (nabla : AffineConnection I M) (X : SmoothVectorField I M)
    {Y Y' : SmoothVectorField I M} {p : M} (h : Y =ᶠ[𝓝 p] Y') :
    nabla.cov X Y p = nabla.cov X Y' p := by
  have hτ : ∀ᶠ q in 𝓝 p, (Y - Y') q = 0 := by
    filter_upwards [h] with q hq
    rw [SmoothVectorField.sub_apply, hq, sub_self]
  have h0 := cov_apply_eq_zero_of_eventuallyEq_zero_right nabla X hτ
  have hsub := nabla.cov_sub_right X Y Y' p
  rw [hsub] at h0
  exact sub_eq_zero.mp h0

/-- **Math.** The covariant derivative of a field locally of the form
`∑ m f_m·Z_m` (with globally smooth scalars `f_m`): Leibniz on each summand,
`(∇_X Y)(p) = ∑_m [X(f_m)(p)·Z_m(p) + f_m(p)·(∇_X Z_m)(p)]`.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem cov_apply_of_eventuallyEq_sum_smul [SigmaCompactSpace M] [T2Space M]
    (nabla : AffineConnection I M) (X : SmoothVectorField I M)
    {ι : Type*} (s : Finset ι) {f : ι → M → ℝ}
    (hf : ∀ m, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f m)) (Z : ι → SmoothVectorField I M)
    {Y : SmoothVectorField I M} {p : M}
    (hY : ∀ᶠ q in 𝓝 p, Y q = ∑ m ∈ s, f m q • Z m q) :
    nabla.cov X Y p
      = ∑ m ∈ s, ((X.dir (f m) p) • Z m p + f m p • nabla.cov X (Z m) p) := by
  classical
  induction s using Finset.induction_on generalizing Y with
  | empty =>
    have h0 : ∀ᶠ q in 𝓝 p, Y q = 0 := by
      filter_upwards [hY] with q hq
      simpa using hq
    simp only [Finset.sum_empty]
    exact cov_apply_eq_zero_of_eventuallyEq_zero_right nabla X h0
  | @insert a s ha ih =>
    set Y' : SmoothVectorField I M := Y - SmoothVectorField.smul (f a) (hf a) (Z a)
      with hY'def
    have hY' : ∀ᶠ q in 𝓝 p, Y' q = ∑ m ∈ s, f m q • Z m q := by
      filter_upwards [hY] with q hq
      rw [hY'def, SmoothVectorField.sub_apply, SmoothVectorField.smul_apply, hq,
        Finset.sum_insert ha]
      abel
    have hIH := ih hY'
    have hYsplit : Y' + SmoothVectorField.smul (f a) (hf a) (Z a) = Y := by
      ext q
      simp only [SmoothVectorField.add_apply, SmoothVectorField.sub_apply, hY'def]
      abel
    rw [← hYsplit, nabla.add_right, SmoothVectorField.add_apply, hIH,
      nabla.leibniz (f a) (hf a) X (Z a) p, Finset.sum_insert ha]
    abel

/-! ### Directional derivatives of chart-pulled-back scalars along the frame -/

/-- **Math.** Differentiating a function of the chart coordinates along the
chart frame computes the coordinate partial derivative:
`X_r(F ∘ φ)(q) = (∂_r F)(φ(q))` when `X_r(q)` is the `r`-th chart frame
vector. Chain rule through `mfderiv_extChartAt_chartBasisVecFiber`.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem mfderiv_comp_extChartAt_chartBasisVecFiber [I.Boundaryless]
    {F : E → ℝ} {α q : M} (hq : q ∈ (chartAt H α).source)
    (hF : DifferentiableAt ℝ F (extChartAt I α q)) (r : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ, ℝ) (fun z => F (extChartAt I α z)) q
        (chartBasisVecFiber (I := I) α r q)
      = partialDeriv (E := E) r F (extChartAt I α q) := by
  have hFdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) F (extChartAt I α q) :=
    hF.mdifferentiableAt
  have hφdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) q :=
    mdifferentiableAt_extChartAt hq
  have hcomp : mfderiv I 𝓘(ℝ, ℝ) (fun z => F (extChartAt I α z)) q
      = (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) F (extChartAt I α q)).comp
          (mfderiv I 𝓘(ℝ, E) (extChartAt I α) q) :=
    mfderiv_comp q hFdiff hφdiff
  rw [hcomp]
  show (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) F (extChartAt I α q))
      (mfderiv I 𝓘(ℝ, E) (extChartAt I α) q (chartBasisVecFiber (I := I) α r q))
    = partialDeriv (E := E) r F (extChartAt I α q)
  rw [mfderiv_extChartAt_chartBasisVecFiber (I := I) α r hq, mfderiv_eq_fderiv]
  rfl

/-! ### The chart-frame Christoffel formula on a neighbourhood -/

/-- **Math.** The chart frame at `α`, extended to global smooth vector fields,
satisfies the **Christoffel formula on a neighbourhood** of any chart point:
there are `X_a ∈ 𝒳(M)` and an open `U ∋ p` inside the chart source with
`X_a = (chart frame)_a` on `U` and
`∇_{X_i} X_j = ∑_m Γ^m_{ij}(φ(·)) X_m` on `U`, for `∇` the Levi-Civita
connection of `g` and `Γ = chartChristoffel`. Neighbourhood upgrade of
`Riemannian.exists_chartFrame_leviCivita_christoffel`.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem exists_chartFrame_leviCivita_christoffel_nhds [I.Boundaryless]
    [SigmaCompactSpace M] [T2Space M]
    (g : RiemannianMetric I M) {α p : M} (hp : p ∈ (chartAt H α).source) :
    ∃ (Z : Fin (Module.finrank ℝ E) → SmoothVectorField I M) (U : Set M),
      IsOpen U ∧ p ∈ U ∧ U ⊆ (chartAt H α).source ∧
      (∀ a, ∀ q ∈ U, Z a q = chartBasisVecFiber (I := I) α a q) ∧
      (∀ i j, ∀ q ∈ U, (g.leviCivitaConnection.cov (Z i) (Z j)) q
        = ∑ m, chartChristoffel (I := I) g α i j m (extChartAt I α q) • Z m q) := by
  classical
  have hbaseopen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hbase : p ∈ (trivializationAt E (TangentSpace I) α).baseSet := hp
  choose Z hZ using fun a : Fin (Module.finrank ℝ E) =>
    exists_smoothVectorField_eventuallyEq (I := I)
      (σ := fun q => chartBasisVecFiber (I := I) α a q)
      (s := (trivializationAt E (TangentSpace I) α).baseSet) hbaseopen
      (chartBasisVec_contMDiffOn (I := I) α a) hbase
  -- extract a common open neighbourhood on which all frame agreements hold
  have hOa : ∀ a, ∃ O : Set M, IsOpen O ∧ p ∈ O ∧
      ∀ q ∈ O, Z a q = chartBasisVecFiber (I := I) α a q := by
    intro a
    obtain ⟨sa, hsa, hsub⟩ := (hZ a).exists_mem
    obtain ⟨O, hOsub, hOopen, hpO⟩ := mem_nhds_iff.mp hsa
    exact ⟨O, hOopen, hpO, fun q hq => hsub q (hOsub hq)⟩
  choose O hOopen hpO hOagree using hOa
  refine ⟨Z, (⋂ a, O a) ∩ ((chartAt H α).source ∩
      (trivializationAt E (TangentSpace I) α).baseSet),
    ((isOpen_iInter_of_finite hOopen).inter
      ((chartAt H α).open_source.inter hbaseopen)),
    ⟨mem_iInter.mpr hpO, hp, hbase⟩,
    fun q hq => hq.2.1, fun a q hq => hOagree a q (mem_iInter.mp hq.1 a), ?_⟩
  intro i j q hq
  have hqO := hq.1
  have hq_source := hq.2.1
  have hq_base := hq.2.2
  have hqOopen : IsOpen (⋂ a, O a) := isOpen_iInter_of_finite hOopen
  -- germ-level agreement of each frame field with the chart frame at `q`
  have hgerm : ∀ a, (fun r => Z a r)
      =ᶠ[𝓝 q] (fun r => chartBasisVecFiber (I := I) α a r) :=
    fun a => eventually_of_mem ((hOopen a).mem_nhds (mem_iInter.mp hqO a))
      (fun r hr => hOagree a r hr)
  have hval : ∀ a, Z a q = chartBasisVecFiber (I := I) α a q :=
    fun a => hOagree a q (mem_iInter.mp hqO a)
  have hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W r => g.koszulDualSection_dual X Y W r)
  have hpe : (extChartAt I α).symm (extChartAt I α q) = q :=
    (extChartAt I α).left_inv (by rwa [extChartAt_source])
  -- the frame brackets vanish at `q`
  have hbr : ∀ a b, DCLieBracket (Z a) (Z b) q = 0 := by
    intro a b
    show VectorField.mlieBracket I (Z a).toFun (Z b).toFun q = 0
    rw [Filter.EventuallyEq.mlieBracket_vectorField_eq (hgerm a) (hgerm b)]
    exact mlieBracket_chartBasisVecFiber_eq_zero (I := I) α a b hq_source
  -- the directional derivative of the Gram entries is the partial derivative
  have hdir : ∀ r a b, (Z r).dir (fun q' => g.metricInner q' (Z a q') (Z b q')) q
      = partialDeriv (E := E) r (chartGramOnE (I := I) g α a b)
          (extChartAt I α q) := by
    intro r a b
    have hfeq : (fun q' => g.metricInner q' (Z a q') (Z b q'))
        =ᶠ[𝓝 q] (fun q' => chartGramMatrix (I := I) g α q' a b) := by
      filter_upwards [hgerm a, hgerm b] with r' hra hrb
      rw [hra, hrb]
      exact (chartGramMatrix_apply (I := I) g α r' a b).symm
    show mfderiv I 𝓘(ℝ, ℝ) (fun q' => g.metricInner q' (Z a q') (Z b q')) q (Z r q)
      = _
    rw [hfeq.mfderiv_eq, hval r]
    exact mfderiv_chartGramMatrix_eq_partialDeriv (I := I) g α a b r hq_source
  exact christoffel_bridge_vector (I := I) g g.leviCivitaConnection hLC α q Z
    hbr hdir hq_base hpe hval i j

/-! ### The chart curvature in Christoffel components -/

/-- **Math.** The Christoffel contraction on chart basis vectors is the
Christoffel symbol: `Γ_y(e_i, e_j) = ∑_k Γ^k_{ij}(y) e_k`.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem chartChristoffelBilin_basis (g : RiemannianMetric I M) (α : M)
    (y : E) (i j : Fin (Module.finrank ℝ E)) :
    chartChristoffelBilin (I := I) g α y (Module.finBasis ℝ E i)
        (Module.finBasis ℝ E j)
      = ∑ k, chartChristoffel (I := I) g α i j k y • Module.finBasis ℝ E k := by
  classical
  rw [chartChristoffelBilin_apply, Geodesic.chartChristoffelContraction_def]
  have hδ : ∀ a b : Fin (Module.finrank ℝ E),
      Geodesic.chartCoord (E := E) a (Module.finBasis ℝ E b)
        = if b = a then (1 : ℝ) else 0 := by
    intro a b
    rw [Geodesic.chartCoord_def, Module.Basis.repr_self, Finsupp.single_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp only [hδ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **Math.** Derivative of the Christoffel contraction in the chart point,
evaluated on basis vectors: `(∂_dΓ)_y(e_i, e_j) = ∑_k (∂_dΓ^k_{ij})(y) e_k`
for `y` interior to the chart target (where each symbol is smooth).
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem fderiv_chartChristoffelBilin_basis (g : RiemannianMetric I M) (α : M)
    {y : E} (hy : y ∈ interior (extChartAt I α).target) (d : E)
    (i j : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (chartChristoffelBilin (I := I) g α) y d (Module.finBasis ℝ E i)
        (Module.finBasis ℝ E j)
      = ∑ k, (fderiv ℝ (chartChristoffel (I := I) g α i j k) y d)
          • Module.finBasis ℝ E k := by
  classical
  have hγdiff : ∀ a b k, HasFDerivAt (chartChristoffel (I := I) g α a b k)
      (fderiv ℝ (chartChristoffel (I := I) g α a b k) y) y := by
    intro a b k
    have h := ((chartChristoffel_contDiffOn_interior (I := I) g α a b k).contDiffAt
      (isOpen_interior.mem_nhds hy)).differentiableAt (by norm_num)
    exact h.hasFDerivAt
  have hD : HasFDerivAt (chartChristoffelBilin (I := I) g α)
      (∑ a, ∑ b, ∑ k,
        ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] E)
            (Geodesic.chartCoordFunctional (E := E) a)).comp
          (ContinuousLinearMap.smulRightL ℝ E E
            (Geodesic.chartCoordFunctional (E := E) b))).comp
        ((fderiv ℝ (chartChristoffel (I := I) g α a b k) y).smulRight
          (Module.finBasis ℝ E k))) y := by
    unfold chartChristoffelBilin
    exact HasFDerivAt.fun_sum fun a _ => HasFDerivAt.fun_sum fun b _ =>
      HasFDerivAt.fun_sum fun k _ => HasFDerivAt.comp
        (g := ⇑((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] E)
            (Geodesic.chartCoordFunctional (E := E) a)).comp
          (ContinuousLinearMap.smulRightL ℝ E E
            (Geodesic.chartCoordFunctional (E := E) b))))
        (f := fun x => chartChristoffel (I := I) g α a b k x • Module.finBasis ℝ E k)
        y (ContinuousLinearMap.hasFDerivAt _)
        ((hγdiff a b k).smul_const (Module.finBasis ℝ E k))
  rw [hD.fderiv]
  have hδ : ∀ a b : Fin (Module.finrank ℝ E),
      Geodesic.chartCoordFunctional (E := E) a (Module.finBasis ℝ E b)
        = if b = a then (1 : ℝ) else 0 := by
    intro a b
    rw [Geodesic.chartCoordFunctional_apply, Geodesic.chartCoord_def,
      Module.Basis.repr_self, Finsupp.single_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRightL_apply_apply, hδ, ite_smul, one_smul, zero_smul,
    apply_ite (fun f : E →L[ℝ] E => f (Module.finBasis ℝ E j)),
    ContinuousLinearMap.zero_apply, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **Math.** **The chart curvature in Christoffel components** — the
classical formula
`ℛ(e_i, e_j)e_k = ∑_m (∂_iΓ^m_{jk} − ∂_jΓ^m_{ik}
+ ∑_r (Γ^r_{jk}Γ^m_{ir} − Γ^r_{ik}Γ^m_{jr})) e_m`
in Morgan–Tian's convention, for `y` interior to the chart target.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem chartCurvature_basis (g : RiemannianMetric I M) (α : M)
    {y : E} (hy : y ∈ interior (extChartAt I α).target)
    (i j k : Fin (Module.finrank ℝ E)) :
    chartCurvature (I := I) g α y (Module.finBasis ℝ E i) (Module.finBasis ℝ E j)
        (Module.finBasis ℝ E k)
      = ∑ m, (partialDeriv (E := E) i (chartChristoffel (I := I) g α j k m) y
            - partialDeriv (E := E) j (chartChristoffel (I := I) g α i k m) y
            + ∑ r, (chartChristoffel (I := I) g α j k r y
                      * chartChristoffel (I := I) g α i r m y
                  - chartChristoffel (I := I) g α i k r y
                      * chartChristoffel (I := I) g α j r m y))
          • Module.finBasis ℝ E m := by
  rw [chartCurvature_def, christoffelCurvature]
  rw [fderiv_chartChristoffelBilin_basis (I := I) g α hy _ j k,
    fderiv_chartChristoffelBilin_basis (I := I) g α hy _ i k,
    chartChristoffelBilin_basis (I := I) g α y j k,
    chartChristoffelBilin_basis (I := I) g α y i k, map_sum, map_sum]
  simp only [map_smul, chartChristoffelBilin_basis (I := I) g α y i,
    chartChristoffelBilin_basis (I := I) g α y j, partialDeriv]
  refine (Module.finBasis ℝ E).ext_elem fun m₀ => ?_
  simp only [map_add, map_sub, map_sum, map_smul, Module.Basis.repr_self,
    Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.coe_add, Finsupp.coe_sub,
    Finsupp.coe_finset_sum, Pi.add_apply, Pi.sub_apply, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_ite, mul_zero,
    mul_one, smul_eq_mul]
  rw [Finset.sum_sub_distrib]
  ring

/-! ### Bilinearity helpers for the metric pairing -/

/-- **Math.** The metric pairing of a finite linear combination, left slot.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem metricInner_sum_smul_left (g : RiemannianMetric I M) (p : M) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (v : ι → TangentSpace I p) (w : TangentSpace I p) :
    g.metricInner p (∑ a ∈ s, c a • v a) w
      = ∑ a ∈ s, c a * g.metricInner p (v a) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [g.metricInner_zero_left]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, g.metricInner_add_left, g.metricInner_smul_left, ih,
      Finset.sum_insert ha]

/-- **Math.** The metric pairing of a finite linear combination, right slot.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem metricInner_sum_smul_right (g : RiemannianMetric I M) (p : M) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (v : TangentSpace I p) (w : ι → TangentSpace I p) :
    g.metricInner p v (∑ a ∈ s, c a • w a)
      = ∑ a ∈ s, c a * g.metricInner p v (w a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [g.metricInner_zero_right]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, g.metricInner_add_right, g.metricInner_smul_right, ih,
      Finset.sum_insert ha]

/-- **Math.** The chart Gram pairing of two basis vectors is the Gram entry:
`⟨e_m, e_l⟩_{G(y)} = G_{ml}(y)`.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem chartMetricInner_basis (g : RiemannianMetric I M) (α : M) (y : E)
    (m l : Fin (Module.finrank ℝ E)) :
    chartMetricInner (I := I) g α y (Module.finBasis ℝ E m) (Module.finBasis ℝ E l)
      = chartGramOnE (I := I) g α m l y := by
  classical
  rw [chartMetricInner_def]
  have hδ : ∀ a b : Fin (Module.finrank ℝ E),
      Geodesic.chartCoord (E := E) a (Module.finBasis ℝ E b)
        = if b = a then (1 : ℝ) else 0 := by
    intro a b
    rw [Geodesic.chartCoord_def, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [hδ, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- **Math.** The metric pairing of chart-frame realizations is the chart Gram
pairing: for `p` in the chart at `α` and `v, w : E`,
`g_p(∑_a v^a X_a(p), ∑_b w^b X_b(p)) = ⟨v, w⟩_{G(φ(p))}`.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem metricInner_chartFrame (g : RiemannianMetric I M) {α p : M}
    (hp : p ∈ (chartAt H α).source) (v w : E) :
    g.metricInner p
        (∑ a, Geodesic.chartCoord (E := E) a v • chartBasisVecFiber (I := I) α a p)
        (∑ b, Geodesic.chartCoord (E := E) b w • chartBasisVecFiber (I := I) α b p)
      = chartMetricInner (I := I) g α (extChartAt I α p) v w := by
  have hpe : (extChartAt I α).symm (extChartAt I α p) = p :=
    (extChartAt I α).left_inv (by rwa [extChartAt_source])
  rw [metricInner_sum_smul_left, chartMetricInner_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [metricInner_sum_smul_right]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hgram : g.metricInner p (chartBasisVecFiber (I := I) α a p)
      (chartBasisVecFiber (I := I) α b p)
      = chartGramOnE (I := I) g α a b (extChartAt I α p) := by
    rw [chartGramOnE, hpe]
    exact chartGramMatrix_apply (I := I) g α p a b ▸ rfl
  rw [hgram]
  ring

/-! ### Multilinearity of the chart curvature in its three slots -/

/-- **Math.** Additivity of the chart curvature in its first slot (general
second and third arguments; the specialization to the Jacobi-operator shape
is `MorganTianLib.chartCurvature_add_left`).
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem chartCurvature_add_fst (g : RiemannianMetric I M) (α : M) (y w z : E)
    (v₁ v₂ : E) :
    chartCurvature (I := I) g α y (v₁ + v₂) w z
      = chartCurvature (I := I) g α y v₁ w z + chartCurvature (I := I) g α y v₂ w z := by
  simp only [chartCurvature_def, christoffelCurvature, map_add,
    ContinuousLinearMap.add_apply]
  abel

/-- **Math.** Homogeneity of the chart curvature in its first slot.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem chartCurvature_smul_fst (g : RiemannianMetric I M) (α : M) (y w z : E)
    (c : ℝ) (v : E) :
    chartCurvature (I := I) g α y (c • v) w z
      = c • chartCurvature (I := I) g α y v w z := by
  simp only [chartCurvature_def, christoffelCurvature, map_smul,
    ContinuousLinearMap.smul_apply, smul_sub, smul_add]

/-- **Math.** Additivity of the chart curvature in its second slot.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem chartCurvature_add_middle (g : RiemannianMetric I M) (α : M) (y v z : E)
    (w₁ w₂ : E) :
    chartCurvature (I := I) g α y v (w₁ + w₂) z
      = chartCurvature (I := I) g α y v w₁ z + chartCurvature (I := I) g α y v w₂ z := by
  simp only [chartCurvature_def, christoffelCurvature, map_add,
    ContinuousLinearMap.add_apply]
  abel

/-- **Math.** Homogeneity of the chart curvature in its second slot.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem chartCurvature_smul_middle (g : RiemannianMetric I M) (α : M) (y v z : E)
    (c : ℝ) (w : E) :
    chartCurvature (I := I) g α y v (c • w) z
      = c • chartCurvature (I := I) g α y v w z := by
  simp only [chartCurvature_def, christoffelCurvature, map_smul,
    ContinuousLinearMap.smul_apply, smul_sub, smul_add]

/-- **Math.** Additivity of the chart curvature in its third slot.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem chartCurvature_add_right (g : RiemannianMetric I M) (α : M) (y v w : E)
    (z₁ z₂ : E) :
    chartCurvature (I := I) g α y v w (z₁ + z₂)
      = chartCurvature (I := I) g α y v w z₁ + chartCurvature (I := I) g α y v w z₂ := by
  simp only [chartCurvature_def, christoffelCurvature, map_add,
    ContinuousLinearMap.add_apply]
  abel

/-- **Math.** Homogeneity of the chart curvature in its third slot.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem chartCurvature_smul_right (g : RiemannianMetric I M) (α : M) (y v w : E)
    (c : ℝ) (z : E) :
    chartCurvature (I := I) g α y v w (c • z)
      = c • chartCurvature (I := I) g α y v w z := by
  simp only [chartCurvature_def, christoffelCurvature, map_smul,
    ContinuousLinearMap.smul_apply, smul_sub, smul_add]

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Math.** The chart curvature of finite linear combinations expands
multilinearly over all three slots.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem chartCurvature_sum₃ (g : RiemannianMetric I M) (α : M) (y : E)
    {ι : Type*} (s : Finset ι) (cv cw cz : ι → ℝ) (e : ι → E) :
    chartCurvature (I := I) g α y (∑ a ∈ s, cv a • e a) (∑ b ∈ s, cw b • e b)
        (∑ c ∈ s, cz c • e c)
      = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, (cv a * cw b * cz c)
          • chartCurvature (I := I) g α y (e a) (e b) (e c) := by
  classical
  have hzero : ∀ w z : E, chartCurvature (I := I) g α y 0 w z = 0 := by
    intro w z
    simp [chartCurvature_def, christoffelCurvature]
  have hzero₂ : ∀ v z : E, chartCurvature (I := I) g α y v 0 z = 0 := by
    intro v z
    simp [chartCurvature_def, christoffelCurvature]
  have hzero₃ : ∀ v w : E, chartCurvature (I := I) g α y v w 0 = 0 := by
    intro v w
    simp [chartCurvature_def, christoffelCurvature]
  have h₁ : ∀ (t : Finset ι) (w z : E),
      chartCurvature (I := I) g α y (∑ a ∈ t, cv a • e a) w z
        = ∑ a ∈ t, cv a • chartCurvature (I := I) g α y (e a) w z := by
    intro t w z
    induction t using Finset.induction_on with
    | empty => simpa using hzero w z
    | @insert a t' ha ih =>
      rw [Finset.sum_insert ha, chartCurvature_add_fst (I := I) g α,
        chartCurvature_smul_fst (I := I) g α, ih, Finset.sum_insert ha]
  have h₂ : ∀ (t : Finset ι) (v z : E),
      chartCurvature (I := I) g α y v (∑ b ∈ t, cw b • e b) z
        = ∑ b ∈ t, cw b • chartCurvature (I := I) g α y v (e b) z := by
    intro t v z
    induction t using Finset.induction_on with
    | empty => simpa using hzero₂ v z
    | @insert b t' hb ih =>
      rw [Finset.sum_insert hb, chartCurvature_add_middle (I := I) g α,
        chartCurvature_smul_middle (I := I) g α, ih, Finset.sum_insert hb]
  have h₃ : ∀ (t : Finset ι) (v w : E),
      chartCurvature (I := I) g α y v w (∑ c ∈ t, cz c • e c)
        = ∑ c ∈ t, cz c • chartCurvature (I := I) g α y v w (e c) := by
    intro t v w
    induction t using Finset.induction_on with
    | empty => simpa using hzero₃ v w
    | @insert c t' hc ih =>
      rw [Finset.sum_insert hc, chartCurvature_add_right (I := I) g α,
        chartCurvature_smul_right (I := I) g α, ih, Finset.sum_insert hc]
  rw [h₁ s]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [h₂ s, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [h₃ s, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_smul, smul_smul]

/-! ### Multilinearity of the pointwise curvature tensor in slots 2–4

Slot-1 additivity/homogeneity is `MorganTianLib.curvatureFormAt_add_left` /
`curvatureFormAt_smul_left` (`MorganTianLib.Ch01.PointwiseCurvature`); the other
three slots follow by the same locality argument. -/

variable [SigmaCompactSpace M] [T2Space M]

/-- **Math.** `curvatureFormAt` is additive in its second slot.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem curvatureFormAt_add_snd [I.Boundaryless] (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (v w₁ w₂ z t : TangentSpace I p) :
    curvatureFormAt g nabla p v (w₁ + w₂) z t
      = curvatureFormAt g nabla p v w₁ z t + curvatureFormAt g nabla p v w₂ z t := by
  have hT := nabla.curvatureForm_isCovariantTensor4 g
  have h1 : nabla.curvatureForm g (extendVector p v) (extendVector p (w₁ + w₂))
        (extendVector p z) (extendVector p t) p
      = nabla.curvatureForm g (extendVector p v)
          (extendVector p w₁ + extendVector p w₂)
          (extendVector p z) (extendVector p t) p :=
    covariantTensor4_congr_apply _ hT rfl (by simp) rfl rfl
  simp only [curvatureFormAt_def]
  rw [h1, hT.add₂]

/-- **Math.** `curvatureFormAt` is homogeneous in its second slot.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem curvatureFormAt_smul_snd [I.Boundaryless] (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (a : ℝ) (v w z t : TangentSpace I p) :
    curvatureFormAt g nabla p v (a • w) z t
      = a * curvatureFormAt g nabla p v w z t := by
  have hT := nabla.curvatureForm_isCovariantTensor4 g
  have hconst : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => a) := contMDiff_const
  have h1 : nabla.curvatureForm g (extendVector p v) (extendVector p (a • w))
        (extendVector p z) (extendVector p t) p
      = nabla.curvatureForm g (extendVector p v)
          (SmoothVectorField.smul (fun _ => a) hconst (extendVector p w))
          (extendVector p z) (extendVector p t) p :=
    covariantTensor4_congr_apply _ hT rfl (by simp) rfl rfl
  simp only [curvatureFormAt_def]
  rw [h1, hT.smul₂]

/-- **Math.** `curvatureFormAt` is additive in its third slot.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem curvatureFormAt_add_trd [I.Boundaryless] (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (v w z₁ z₂ t : TangentSpace I p) :
    curvatureFormAt g nabla p v w (z₁ + z₂) t
      = curvatureFormAt g nabla p v w z₁ t + curvatureFormAt g nabla p v w z₂ t := by
  have hT := nabla.curvatureForm_isCovariantTensor4 g
  have h1 : nabla.curvatureForm g (extendVector p v) (extendVector p w)
        (extendVector p (z₁ + z₂)) (extendVector p t) p
      = nabla.curvatureForm g (extendVector p v) (extendVector p w)
          (extendVector p z₁ + extendVector p z₂) (extendVector p t) p :=
    covariantTensor4_congr_apply _ hT rfl rfl (by simp) rfl
  simp only [curvatureFormAt_def]
  rw [h1, hT.add₃]

/-- **Math.** `curvatureFormAt` is homogeneous in its third slot.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem curvatureFormAt_smul_trd [I.Boundaryless] (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (a : ℝ) (v w z t : TangentSpace I p) :
    curvatureFormAt g nabla p v w (a • z) t
      = a * curvatureFormAt g nabla p v w z t := by
  have hT := nabla.curvatureForm_isCovariantTensor4 g
  have hconst : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => a) := contMDiff_const
  have h1 : nabla.curvatureForm g (extendVector p v) (extendVector p w)
        (extendVector p (a • z)) (extendVector p t) p
      = nabla.curvatureForm g (extendVector p v) (extendVector p w)
          (SmoothVectorField.smul (fun _ => a) hconst (extendVector p z))
          (extendVector p t) p :=
    covariantTensor4_congr_apply _ hT rfl rfl (by simp) rfl
  simp only [curvatureFormAt_def]
  rw [h1, hT.smul₃]

/-- **Math.** `curvatureFormAt` is additive in its fourth slot.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem curvatureFormAt_add_fth [I.Boundaryless] (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (v w z t₁ t₂ : TangentSpace I p) :
    curvatureFormAt g nabla p v w z (t₁ + t₂)
      = curvatureFormAt g nabla p v w z t₁ + curvatureFormAt g nabla p v w z t₂ := by
  have hT := nabla.curvatureForm_isCovariantTensor4 g
  have h1 : nabla.curvatureForm g (extendVector p v) (extendVector p w)
        (extendVector p z) (extendVector p (t₁ + t₂)) p
      = nabla.curvatureForm g (extendVector p v) (extendVector p w)
          (extendVector p z) (extendVector p t₁ + extendVector p t₂) p :=
    covariantTensor4_congr_apply _ hT rfl rfl rfl (by simp)
  simp only [curvatureFormAt_def]
  rw [h1, hT.add₄]

/-- **Math.** `curvatureFormAt` is homogeneous in its fourth slot.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem curvatureFormAt_smul_fth [I.Boundaryless] (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (a : ℝ) (v w z t : TangentSpace I p) :
    curvatureFormAt g nabla p v w z (a • t)
      = a * curvatureFormAt g nabla p v w z t := by
  have hT := nabla.curvatureForm_isCovariantTensor4 g
  have hconst : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => a) := contMDiff_const
  have h1 : nabla.curvatureForm g (extendVector p v) (extendVector p w)
        (extendVector p z) (extendVector p (a • t)) p
      = nabla.curvatureForm g (extendVector p v) (extendVector p w)
          (extendVector p z)
          (SmoothVectorField.smul (fun _ => a) hconst (extendVector p t)) p :=
    covariantTensor4_congr_apply _ hT rfl rfl rfl (by simp)
  simp only [curvatureFormAt_def]
  rw [h1, hT.smul₄]

/-- **Math.** The pointwise curvature tensor of four finite linear
combinations expands quadrilinearly.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem curvatureFormAt_sum₄ [I.Boundaryless] (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) {ι : Type*} (s : Finset ι)
    (cv cw cz ct : ι → ℝ) (e : ι → TangentSpace I p) :
    curvatureFormAt g nabla p (∑ a ∈ s, cv a • e a) (∑ b ∈ s, cw b • e b)
        (∑ c ∈ s, cz c • e c) (∑ d ∈ s, ct d • e d)
      = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, cv a * cw b * cz c * ct d
          * curvatureFormAt g nabla p (e a) (e b) (e c) (e d) := by
  classical
  have hzero₁ : ∀ w z t, curvatureFormAt g nabla p 0 w z t = 0 := by
    intro w z t
    have h := curvatureFormAt_smul_left g nabla p 0 0 w z t
    simpa using h
  have hzero₂ : ∀ v z t, curvatureFormAt g nabla p v 0 z t = 0 := by
    intro v z t
    have h := curvatureFormAt_smul_snd g nabla p 0 v 0 z t
    simpa using h
  have hzero₃ : ∀ v w t, curvatureFormAt g nabla p v w 0 t = 0 := by
    intro v w t
    have h := curvatureFormAt_smul_trd g nabla p 0 v w 0 t
    simpa using h
  have hzero₄ : ∀ v w z, curvatureFormAt g nabla p v w z 0 = 0 := by
    intro v w z
    have h := curvatureFormAt_smul_fth g nabla p 0 v w z 0
    simpa using h
  have h₁ : ∀ (u : Finset ι) (w z t : TangentSpace I p),
      curvatureFormAt g nabla p (∑ a ∈ u, cv a • e a) w z t
        = ∑ a ∈ u, cv a * curvatureFormAt g nabla p (e a) w z t := by
    intro u w z t
    induction u using Finset.induction_on with
    | empty => simpa using hzero₁ w z t
    | @insert a u' ha ih =>
      rw [Finset.sum_insert ha, curvatureFormAt_add_left,
        curvatureFormAt_smul_left, ih, Finset.sum_insert ha]
  have h₂ : ∀ (u : Finset ι) (v z t : TangentSpace I p),
      curvatureFormAt g nabla p v (∑ b ∈ u, cw b • e b) z t
        = ∑ b ∈ u, cw b * curvatureFormAt g nabla p v (e b) z t := by
    intro u v z t
    induction u using Finset.induction_on with
    | empty => simpa using hzero₂ v z t
    | @insert b u' hb ih =>
      rw [Finset.sum_insert hb, curvatureFormAt_add_snd,
        curvatureFormAt_smul_snd, ih, Finset.sum_insert hb]
  have h₃ : ∀ (u : Finset ι) (v w t : TangentSpace I p),
      curvatureFormAt g nabla p v w (∑ c ∈ u, cz c • e c) t
        = ∑ c ∈ u, cz c * curvatureFormAt g nabla p v w (e c) t := by
    intro u v w t
    induction u using Finset.induction_on with
    | empty => simpa using hzero₃ v w t
    | @insert c u' hc ih =>
      rw [Finset.sum_insert hc, curvatureFormAt_add_trd,
        curvatureFormAt_smul_trd, ih, Finset.sum_insert hc]
  have h₄ : ∀ (u : Finset ι) (v w z : TangentSpace I p),
      curvatureFormAt g nabla p v w z (∑ d ∈ u, ct d • e d)
        = ∑ d ∈ u, ct d * curvatureFormAt g nabla p v w z (e d) := by
    intro u v w z
    induction u using Finset.induction_on with
    | empty => simpa using hzero₄ v w z
    | @insert d u' hd ih =>
      rw [Finset.sum_insert hd, curvatureFormAt_add_fth,
        curvatureFormAt_smul_fth, ih, Finset.sum_insert hd]
  rw [h₁ s]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [h₂ s, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [h₃ s, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [h₄ s, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

end MorganTianLib

end
