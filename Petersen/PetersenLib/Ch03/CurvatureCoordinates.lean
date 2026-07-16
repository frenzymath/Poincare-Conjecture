import PetersenLib.Ch02.ChristoffelSymbols
import PetersenLib.Ch03.CurvaturePointwise

/-!
# Petersen Ch. 3, §3.1.6 — Curvature in Local Coordinates

The coordinate formula for the curvature tensor
(prop:pet-ch3-curvature-coordinate-formula): writing
`R(∂_i, ∂_j)∂_k = R^l_{ijk} ∂_l` in the chart frame at `p`, the coefficients are
`R^l_{ijk} = ∂_i Γ^l_{jk} − ∂_j Γ^l_{ik} + Γ^s_{jk} Γ^l_{is} − Γ^s_{ik} Γ^l_{js}`
(`curvatureTensor_coordinates`).

## Design notes

* The moving Christoffel symbol `Γ^l_{jk}(q)`, for `q` in the **fixed** chart at
  `p`, is the chart-coordinate function `chartChristoffel g p j k l` evaluated at
  the chart image `extChartAt I p q`; at `q = p` it agrees with the abstract
  symbols `christoffelSymbolsSecondKind` by `christoffelSymbols_metric_formula`.
  Consequently `∂_i Γ^l_{jk}` is the chart partial derivative
  `partialDeriv i (chartChristoffel g p j k l)` at `extChartAt I p p` — the same
  reading in which `∂_i g_{jk}` appears in `christoffelSymbolsFirstKind`.
* The chapter's connection differentiates global smooth fields, so the chart
  frame `∂_j = chartBasisVecFiber p j` is fed to it through a global smooth field
  `chartFrameField p j` agreeing with `∂_j` near `p`
  (`exists_smoothVectorField_eventuallyEq`); similarly the coefficient functions
  `Γ^l_{jk}(·)` are fed to the Leibniz rule through global smooth functions
  agreeing with them near `p` (`exists_contMDiff_eventuallyEq`). Locality of the
  connection (`connection_local_openSet`) makes all choices irrelevant.
* The proof is Petersen's direct expansion: near `p` the field identity
  `∇_{∂_j}∂_k = Γ^s_{jk} ∂_s` holds at every point of the chart
  (`leviCivita_cov_chartFrameField_expansion`, a moving-point Koszul collapse);
  differentiating it along `∂_i` by the Leibniz rule and using `[∂_i, ∂_j] = 0`
  gives the formula.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.6.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Function Finset
open scoped Manifold Topology ContDiff Matrix

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [LocallyCompactSpace M]

/-! ## Local-to-global extension of germs of smooth functions -/

/-- **Eng.** A function smooth on an open set `s` agrees near any `x ∈ s` with a
globally smooth function: cut off by a bump that is `1` near `x` and supported in
`s`. Function counterpart of `exists_smoothVectorField_eventuallyEq`. -/
theorem exists_contMDiff_eventuallyEq {f : M → ℝ} {s : Set M} (hs : IsOpen s)
    (hf : ContMDiffOn I 𝓘(ℝ) ∞ f s) {x : M} (hx : x ∈ s) :
    ∃ F : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ F ∧ F =ᶠ[nhds x] f := by
  classical
  -- a closed neighborhood `K ⊆ s`, and a closed neighborhood `K' ⊆ interior K`
  obtain ⟨K, hK_nhds, hK_closed, hK_sub⟩ :=
    exists_mem_nhds_isClosed_subset (hs.mem_nhds hx)
  obtain ⟨K', hK'_nhds, hK'_closed, hK'_sub⟩ :=
    exists_mem_nhds_isClosed_subset
      (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hK_nhds))
  -- a cutoff: `0` outside `interior K`, `1` on `K'`
  obtain ⟨lam, hlam0, hlam1, -⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed I
      (isClosed_compl_iff.mpr isOpen_interior) hK'_closed
      (by rw [Set.disjoint_compl_left_iff_subset]; exact hK'_sub)
  refine ⟨fun q => if q ∈ s then (lam : M → ℝ) q * f q else 0, ?_, ?_⟩
  · intro q
    by_cases hq : q ∈ s
    · have hsmul : ContMDiffOn I 𝓘(ℝ) ∞ (fun q' => (lam : M → ℝ) q' * f q') s :=
        (lam.contMDiff.contMDiffOn).mul hf
      have hcongr : ContMDiffOn I 𝓘(ℝ) ∞
          (fun q' => if q' ∈ s then (lam : M → ℝ) q' * f q' else 0) s :=
        hsmul.congr fun q' hq' => if_pos hq'
      exact (hcongr q hq).contMDiffAt (hs.mem_nhds hq)
    · have hqK : q ∉ K := fun h => hq (hK_sub h)
      have hzero : ∀ q' ∈ (Kᶜ : Set M),
          (if q' ∈ s then (lam : M → ℝ) q' * f q' else 0) = 0 := by
        intro q' hq'
        by_cases hq's : q' ∈ s
        · rw [if_pos hq's]
          have hlamq' : (lam : M → ℝ) q' = 0 := by
            have hq'int : q' ∉ interior K := fun h => hq' (interior_subset h)
            simpa using hlam0 (Set.mem_compl hq'int)
          rw [hlamq', zero_mul]
        · rw [if_neg hq's]
      exact (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (eventuallyEq_of_mem (hK_closed.isOpen_compl.mem_nhds hqK) hzero)
  · filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hK'_nhds)]
      with q hq
    have hqK' : q ∈ K' := interior_subset hq
    have hqs : q ∈ s := hK_sub (interior_subset (hK'_sub hqK'))
    rw [if_pos hqs, show (lam : M → ℝ) q = 1 from by simpa using hlam1 hqK', one_mul]

/-! ## The chart frame as global smooth fields -/

/-- **Eng.** A global smooth vector field agreeing with the coordinate frame
field `∂_j = chartBasisVecFiber p j` on a neighborhood of `p`
(`exists_smoothVectorField_eventuallyEq`) — a public analogue of the frame
extension used to define `christoffelSymbolsSecondKind`. The choice is
irrelevant near `p` by locality of the connection. -/
def chartFrameField (p : M) (j : Fin (Module.finrank ℝ E)) :
    SmoothVectorField I M :=
  (exists_smoothVectorField_eventuallyEq (I := I)
    (σ := fun q => chartBasisVecFiber (I := I) p j q)
    (trivializationAt E (TangentSpace I) p).open_baseSet
    (chartBasisVec_contMDiffOn (I := I) p j)
    (FiberBundle.mem_baseSet_trivializationAt' p)).choose

/-- **Eng.** The defining property of `chartFrameField`: it agrees with the
coordinate frame field near `p`. -/
theorem chartFrameField_eventuallyEq (p : M) (j : Fin (Module.finrank ℝ E)) :
    ⇑(chartFrameField (I := I) p j)
      =ᶠ[nhds p] fun q => chartBasisVecFiber (I := I) p j q :=
  (exists_smoothVectorField_eventuallyEq (I := I)
    (σ := fun q => chartBasisVecFiber (I := I) p j q)
    (trivializationAt E (TangentSpace I) p).open_baseSet
    (chartBasisVec_contMDiffOn (I := I) p j)
    (FiberBundle.mem_baseSet_trivializationAt' p)).choose_spec

theorem chartFrameField_apply_self (p : M) (j : Fin (Module.finrank ℝ E)) :
    chartFrameField (I := I) p j p = chartBasisVecFiber (I := I) p j p :=
  (chartFrameField_eventuallyEq (I := I) p j).self_of_nhds

/-! ## Bilinear expansions of the metric against finite sums -/

/-- **Eng.** `g(Σ c_m • w_m, v) = Σ c_m g(w_m, v)`. -/
private theorem metricInner_sum_smul_left (g : RiemannianMetric I M) (x : M)
    {n : ℕ} (c : Fin n → ℝ) (w : Fin n → TangentSpace I x) (v : TangentSpace I x) :
    g.metricInner x (∑ m, c m • w m) v = ∑ m, c m * g.metricInner x (w m) v := by
  show (g.inner x) (∑ m, c m • w m) v = _
  rw [map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

/-- **Eng.** `g(v, Σ c_m • w_m) = Σ c_m g(v, w_m)`. -/
private theorem metricInner_sum_smul_right (g : RiemannianMetric I M) (x : M)
    {n : ℕ} (v : TangentSpace I x) (c : Fin n → ℝ) (w : Fin n → TangentSpace I x) :
    g.metricInner x v (∑ m, c m • w m) = ∑ m, c m * g.metricInner x v (w m) := by
  show (g.inner x v) (∑ m, c m • w m) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

/-- **Eng.** Symmetry of the chart Gram entries under the chart partial
derivative: `∂_r G_{ab} = ∂_r G_{ba}`. -/
private theorem partialDeriv_chartGramOnE_symm (g : RiemannianMetric I M)
    (α : M) (a b r : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) r (chartGramOnE (I := I) g α a b) y
      = partialDeriv (E := E) r (chartGramOnE (I := I) g α b a) y := by
  unfold partialDeriv
  rw [show chartGramOnE (I := I) g α a b = chartGramOnE (I := I) g α b a from
    funext fun z => chartGramOnE_symm (I := I) g α a b z]

/-! ## The chart partial derivative of the moving Christoffel symbols -/

/-- **Math.** The manifold derivative of the moving Christoffel symbol
`q ↦ Γ^c_{ab}(q)` (the fixed-chart function `chartChristoffel g p a b c`
composed with the chart) along the frame vector `∂_r` is the chart partial
derivative `∂_r Γ^c_{ab}` — the chart chain rule through
`mfderiv_extChartAt_chartBasisVecFiber`, using smoothness of the coordinate
Christoffel symbols (`chartChristoffel_contDiffOn_interior`). -/
theorem mfderiv_chartChristoffel_eq_partialDeriv (g : RiemannianMetric I M)
    (p : M) (a b c r : Fin (Module.finrank ℝ E)) {q : M}
    (hq : q ∈ (chartAt H p).source) :
    mfderiv I 𝓘(ℝ) (fun x => chartChristoffel (I := I) g p a b c (extChartAt I p x)) q
        (chartBasisVecFiber (I := I) p r q)
      = partialDeriv (E := E) r (chartChristoffel (I := I) g p a b c)
          (extChartAt I p q) := by
  have hqsrc : q ∈ (extChartAt I p).source := by rwa [extChartAt_source]
  have hy : extChartAt I p q ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hqsrc
  have hΓdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
      (chartChristoffel (I := I) g p a b c) (extChartAt I p q) := by
    have hnb : interior (extChartAt I p).target ∈ nhds (extChartAt I p q) :=
      Filter.mem_of_superset (extChartAt_target_mem_nhds' (I := I) hy)
        (extChartAt_target_subset_interior_of_boundaryless (I := I) p)
    have hcd : ContDiffAt ℝ ∞ (chartChristoffel (I := I) g p a b c)
        (extChartAt I p q) :=
      (chartChristoffel_contDiffOn_interior (I := I) g p a b c).contDiffAt hnb
    exact hcd.contMDiffAt.mdifferentiableAt (by decide)
  have hφdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I p) q :=
    mdifferentiableAt_extChartAt hq
  rw [show (fun x => chartChristoffel (I := I) g p a b c (extChartAt I p x))
      = (chartChristoffel (I := I) g p a b c) ∘ (extChartAt I p) from rfl,
    mfderiv_comp q hΓdiff hφdiff]
  show (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (chartChristoffel (I := I) g p a b c) (extChartAt I p q))
      (mfderiv I 𝓘(ℝ, E) (extChartAt I p) q (chartBasisVecFiber (I := I) p r q))
    = partialDeriv (E := E) r (chartChristoffel (I := I) g p a b c) (extChartAt I p q)
  rw [mfderiv_extChartAt_chartBasisVecFiber (I := I) p r hq, mfderiv_eq_fderiv]
  rfl

/-! ## The moving-point frame expansion `∇_{∂_i}∂_j = Γ^m_{ij} ∂_m` -/

section MovingFrame

variable (g : RiemannianMetric I M) (p : M)

/-- **Eng.** The frame fields have vanishing pairwise Lie brackets at every
point where they agree with the chart frame: the bracket only sees germs, and
`[∂_a, ∂_b] = 0` on the chart (`mlieBracket_chartBasisVecFiber_eq_zero`). -/
private theorem lieDerivative_chartFrameField_eq_zero
    (a b : Fin (Module.finrank ℝ E)) {q : M} (hq : q ∈ (chartAt H p).source)
    (heva : ⇑(chartFrameField (I := I) p a)
      =ᶠ[nhds q] fun x => chartBasisVecFiber (I := I) p a x)
    (hevb : ⇑(chartFrameField (I := I) p b)
      =ᶠ[nhds q] fun x => chartBasisVecFiber (I := I) p b x) :
    lieDerivativeVectorField I (⇑(chartFrameField (I := I) p a))
      (⇑(chartFrameField (I := I) p b)) q = 0 := by
  rw [lieDerivativeVectorField_eq_mlieBracket,
    Filter.EventuallyEq.mlieBracket_vectorField_eq heva hevb]
  exact mlieBracket_chartBasisVecFiber_eq_zero (I := I) p a b hq

/-- **Eng.** The directional derivative of the metric components along the
frame is the chart partial derivative of the Gram matrix, at every point where
the frame fields agree with the chart frame. -/
private theorem directionalDerivative_chartFrameField_metric
    (r a b : Fin (Module.finrank ℝ E)) {q : M} (hq : q ∈ (chartAt H p).source)
    (hev : ∀ m, ⇑(chartFrameField (I := I) p m)
      =ᶠ[nhds q] fun x => chartBasisVecFiber (I := I) p m x) :
    directionalDerivative (⇑(chartFrameField (I := I) p r))
      (fun x => g.metricInner x (chartFrameField (I := I) p a x)
        (chartFrameField (I := I) p b x)) q
      = partialDeriv (E := E) r (chartGramOnE (I := I) g p a b) (extChartAt I p q) := by
  have hevG : (fun x => g.metricInner x (chartFrameField (I := I) p a x)
      (chartFrameField (I := I) p b x))
      =ᶠ[nhds q] fun x => chartGramMatrix (I := I) g p x a b := by
    filter_upwards [hev a, hev b] with x hxa hxb
    rw [hxa, hxb]
    rfl
  have hrq : ⇑(chartFrameField (I := I) p r) q = chartBasisVecFiber (I := I) p r q :=
    (hev r).self_of_nhds
  rw [directionalDerivative_apply, hevG.mfderiv_eq, hrq]
  exact mfderiv_chartGramMatrix_eq_partialDeriv (I := I) g p a b r hq

/-- **Eng.** The Koszul formula collapsed on the frame at a moving point `q` of
the chart at `p`:
`2 g(∇_{∂_i}∂_j, ∂_l)|_q = (∂_i g_{lj} + ∂_j g_{li} − ∂_l g_{ij})(extChartAt I p q)`. -/
private theorem koszul_chartFrameField_collapse
    (i j l : Fin (Module.finrank ℝ E)) {q : M} (hq : q ∈ (chartAt H p).source)
    (hev : ∀ m, ⇑(chartFrameField (I := I) p m)
      =ᶠ[nhds q] fun x => chartBasisVecFiber (I := I) p m x) :
    2 * g.metricInner q
        ((g.leviCivita).cov q (chartBasisVecFiber (I := I) p i q)
          (⇑(chartFrameField (I := I) p j)))
        (chartBasisVecFiber (I := I) p l q)
      = partialDeriv (E := E) i (chartGramOnE (I := I) g p l j) (extChartAt I p q)
        + partialDeriv (E := E) j (chartGramOnE (I := I) g p l i) (extChartAt I p q)
        - partialDeriv (E := E) l (chartGramOnE (I := I) g p i j) (extChartAt I p q) := by
  have hsmi : IsSmoothVectorField
      (⇑(chartFrameField (I := I) p i) : Π x : M, TangentSpace I x) :=
    (chartFrameField (I := I) p i).smooth
  have hsmj : IsSmoothVectorField
      (⇑(chartFrameField (I := I) p j) : Π x : M, TangentSpace I x) :=
    (chartFrameField (I := I) p j).smooth
  have hsml : IsSmoothVectorField
      (⇑(chartFrameField (I := I) p l) : Π x : M, TangentSpace I x) :=
    (chartFrameField (I := I) p l).smooth
  -- Koszul's formula with `X = ∂_j`, `Y = ∂_i`, `Z = ∂_l` (frame fields).
  have hK := (g.leviCivita).koszul hsmj hsmi hsml q
  unfold koszulExpression at hK
  -- The three bracket terms vanish.
  rw [lieDerivative_chartFrameField_eq_zero (I := I) p j i hq (hev j) (hev i),
    lieDerivative_chartFrameField_eq_zero (I := I) p i l hq (hev i) (hev l),
    lieDerivative_chartFrameField_eq_zero (I := I) p l j hq (hev l) (hev j),
    g.metricInner_zero_left, g.metricInner_zero_left, g.metricInner_zero_left] at hK
  -- The three directional derivatives become Gram partial derivatives.
  rw [directionalDerivative_chartFrameField_metric (I := I) g p j i l hq hev,
    directionalDerivative_chartFrameField_metric (I := I) g p i j l hq hev,
    directionalDerivative_chartFrameField_metric (I := I) g p l j i hq hev] at hK
  -- Evaluate the frame fields at `q`.
  rw [(hev i).self_of_nhds, (hev l).self_of_nhds] at hK
  have s1 := partialDeriv_chartGramOnE_symm (I := I) g p i l j (extChartAt I p q)
  have s2 := partialDeriv_chartGramOnE_symm (I := I) g p j l i (extChartAt I p q)
  have s3 := partialDeriv_chartGramOnE_symm (I := I) g p j i l (extChartAt I p q)
  linarith [hK, s1, s2, s3]

/-- **Eng.** The inner form of the moving-point expansion: contracting with the
Gram matrix, `g(∇_{∂_i}∂_j, ∂_l)|_q = Σ_m g_{lm}(q) Γ^m_{ij}(q)`. -/
private theorem metricInner_cov_chartFrameField
    (i j l : Fin (Module.finrank ℝ E)) {q : M} (hq : q ∈ (chartAt H p).source)
    (hev : ∀ m, ⇑(chartFrameField (I := I) p m)
      =ᶠ[nhds q] fun x => chartBasisVecFiber (I := I) p m x) :
    g.metricInner q
        ((g.leviCivita).cov q (chartBasisVecFiber (I := I) p i q)
          (⇑(chartFrameField (I := I) p j)))
        (chartBasisVecFiber (I := I) p l q)
      = ∑ m, chartGramOnE (I := I) g p l m (extChartAt I p q)
          * chartChristoffel (I := I) g p i j m (extChartAt I p q) := by
  have hqsrc : q ∈ (extChartAt I p).source := by rwa [extChartAt_source]
  have hqe : (extChartAt I p).symm (extChartAt I p q) = q :=
    (extChartAt I p).left_inv hqsrc
  have hy : (extChartAt I p).symm (extChartAt I p q)
      ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [hqe, trivializationAt_baseSet_eq_chartAt_source]
    exact hq
  have hc := chartGram_christoffel_contraction (I := I) g p l i j
    (extChartAt I p q) hy
  have hk := koszul_chartFrameField_collapse (I := I) g p i j l hq hev
  linarith

/-- **Math.** The **moving-point frame expansion of the connection**
(`∇_{∂_i}∂_j = Γ^m_{ij} ∂_m` as an identity at every point of the chart at
`p`): at any `q` in the chart at `p` where the global frame fields agree with
the chart frame,
`∇_{∂_i|_q}(chartFrameField p j) = Σ_m Γ^m_{ij}(q) ∂_m|_q`,
with `Γ^m_{ij}(q) = chartChristoffel g p i j m (extChartAt I p q)` the
coordinate Christoffel symbols of the **fixed** chart at `p`. -/
theorem leviCivita_cov_chartFrameField_expansion
    (i j : Fin (Module.finrank ℝ E)) {q : M} (hq : q ∈ (chartAt H p).source)
    (hev : ∀ m, ⇑(chartFrameField (I := I) p m)
      =ᶠ[nhds q] fun x => chartBasisVecFiber (I := I) p m x) :
    (g.leviCivita).cov q (chartBasisVecFiber (I := I) p i q)
        (⇑(chartFrameField (I := I) p j))
      = ∑ m, chartChristoffel (I := I) g p i j m (extChartAt I p q) •
          chartBasisVecFiber (I := I) p m q := by
  classical
  have hqb : q ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hq
  have hqsrc : q ∈ (extChartAt I p).source := by rwa [extChartAt_source]
  have hqe : (extChartAt I p).symm (extChartAt I p q) = q :=
    (extChartAt I p).left_inv hqsrc
  have hgram : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g p a b (extChartAt I p q)
        = g.metricInner q (chartBasisVecFiber (I := I) p a q)
            (chartBasisVecFiber (I := I) p b q) := by
    intro a b
    rw [chartGramOnE_def, hqe]
    rfl
  refine (g.metricInner_eq_iff_eq q _ _).mp fun Z => ?_
  have key : ∀ m : Fin (Module.finrank ℝ E),
      g.metricInner q ((g.leviCivita).cov q (chartBasisVecFiber (I := I) p i q)
          (⇑(chartFrameField (I := I) p j)))
        (chartBasisVecFiber (I := I) p m q)
      = g.metricInner q
          (∑ a, chartChristoffel (I := I) g p i j a (extChartAt I p q) •
            chartBasisVecFiber (I := I) p a q)
          (chartBasisVecFiber (I := I) p m q) := by
    intro m
    rw [metricInner_cov_chartFrameField (I := I) g p i j m hq hev,
      metricInner_sum_smul_left]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hgram m a, mul_comm]
    congr 1
    exact g.metricInner_comm q _ _
  have hZ : Z = ∑ m, ((chartBasisFamily (I := I) p hqb).repr Z m) •
      chartBasisVecFiber (I := I) p m q := by
    conv_lhs => rw [← (chartBasisFamily (I := I) p hqb).sum_repr Z]
    exact Finset.sum_congr rfl fun m _ => by rw [chartBasisFamily_apply]
  rw [hZ, metricInner_sum_smul_right, metricInner_sum_smul_right]
  exact Finset.sum_congr rfl fun m _ => by rw [key m]

end MovingFrame

/-! ## The covariant derivative of a frame combination -/

/-- **Eng.** The covariant derivative of a finite sum of function-scaled smooth
fields: `∇_v (Σ_m f_m • V_m) = Σ_m (df_m(v) • V_m|_p + f_m(p) • ∇_v V_m)` —
additivity plus the Leibniz rule. -/
theorem AffineConnection.cov_finsetSum_smul_field (D : AffineConnection I M)
    (p : M) (v : TangentSpace I p) {ι : Type*} (s : Finset ι)
    (f : ι → M → ℝ) (V : ι → Π x : M, TangentSpace I x)
    (hf : ∀ m, ContMDiff I 𝓘(ℝ) ∞ (f m)) (hV : ∀ m, IsSmoothVectorField (V m)) :
    D.cov p v (fun q => ∑ m ∈ s, f m q • V m q)
      = ∑ m ∈ s, (dirTangent (f m) v • V m p + f m p • D.cov p v (V m)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have e : (fun q => ∑ m ∈ (∅ : Finset ι), f m q • V m q)
          = fun q : M => (0 : TangentSpace I q) := by
        funext q; simp
      rw [e, D.cov_zero_field]
      simp
  | insert a s ha ih =>
      have hterm : ∀ m, IsSmoothVectorField (fun q => f m q • V m q) := fun m => by
        simpa using (SmoothVectorField.smul (f m) (hf m) ⟨V m, hV m⟩).smooth
      have hsum : IsSmoothVectorField (fun q => ∑ m ∈ s, f m q • V m q) :=
        isSmoothVectorField_finsetSum s _ hterm
      have e : (fun q => ∑ m ∈ insert a s, f m q • V m q)
          = fun q => f a q • V a q + ∑ m ∈ s, f m q • V m q := by
        funext q; exact Finset.sum_insert ha
      rw [e, D.add_field p v (hterm a) hsum, D.leibniz p v (hf a) (hV a), ih,
        Finset.sum_insert ha]

/-! ## The curvature coordinate formula -/

section CurvatureCoordinates

variable (g : RiemannianMetric I M) (p : M)

/-- **Eng.** The double covariant derivative of the frame at `p`:
`∇_{∂_i}∇_{∂_j}∂_k |_p = Σ_l (∂_i Γ^l_{jk} + Σ_s Γ^s_{jk} Γ^l_{is}) ∂_l |_p`.
This is the Leibniz expansion of `∇_{∂_i}(Γ^s_{jk} ∂_s)` at `p`, after replacing
the smooth field `∇_{∂_j}∂_k` near `p` by the frame combination
`Σ_s Γ^s_{jk}(·) ∂_s` through locality of the connection. -/
private theorem leviCivita_cov_cov_chartFrameField
    (i j k : Fin (Module.finrank ℝ E)) :
    (g.leviCivita).toAffineConnection.cov p (chartBasisVecFiber (I := I) p i p)
        ((g.leviCivita).toAffineConnection.covField
          (⇑(chartFrameField (I := I) p j)) (⇑(chartFrameField (I := I) p k)))
      = ∑ l, (partialDeriv (E := E) i (chartChristoffel (I := I) g p j k l)
              (extChartAt I p p)
            + ∑ s, christoffelSymbolsSecondKind g p j k s *
                christoffelSymbolsSecondKind g p i s l)
          • chartBasisVecFiber (I := I) p l p := by
  classical
  -- the moving Christoffel coefficient functions, in the fixed chart at `p`
  set Γ : Fin (Module.finrank ℝ E) → M → ℝ :=
    fun m x => chartChristoffel (I := I) g p j k m (extChartAt I p x) with hΓ
  -- they are smooth on the chart source
  have hΓsmooth : ∀ m, ContMDiffOn I 𝓘(ℝ) ∞ (Γ m) (chartAt H p).source := by
    intro m
    have hΓE : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (chartChristoffel (I := I) g p j k m)
        (interior (extChartAt I p).target) :=
      (chartChristoffel_contDiffOn_interior (I := I) g p j k m).contMDiffOn
    have hsub : (chartAt H p).source ⊆
        extChartAt I p ⁻¹' (interior (extChartAt I p).target) := by
      intro q hq
      exact extChartAt_target_subset_interior_of_boundaryless (I := I) p
        ((extChartAt I p).map_source (by rwa [extChartAt_source]))
    exact hΓE.comp (contMDiffOn_extChartAt (I := I) (x := p) (n := ∞)) hsub
  -- global smooth functions agreeing with them near `p`
  choose γ hγsmooth hγev using fun m =>
    exists_contMDiff_eventuallyEq (I := I) ((chartAt H p).open_source)
      (hΓsmooth m) (mem_chart_source H p)
  -- the frame combination field
  have hterm : ∀ m, IsSmoothVectorField
      (fun q => γ m q • ⇑(chartFrameField (I := I) p m) q) := fun m => by
    simpa using
      (SmoothVectorField.smul (γ m) (hγsmooth m) (chartFrameField (I := I) p m)).smooth
  have hW : IsSmoothVectorField
      (fun q => ∑ m, γ m q • ⇑(chartFrameField (I := I) p m) q) :=
    isSmoothVectorField_finsetSum Finset.univ _ hterm
  have hcovjk : IsSmoothVectorField
      ((g.leviCivita).toAffineConnection.covField
        (⇑(chartFrameField (I := I) p j)) (⇑(chartFrameField (I := I) p k))) :=
    (g.leviCivita).smooth_cov (chartFrameField (I := I) p j).smooth
      (chartFrameField (I := I) p k).smooth
  -- an open neighborhood of `p` on which everything agrees
  obtain ⟨U, hU, hUopen, hpU⟩ := eventually_nhds_iff.mp
    (((eventually_all.mpr fun m => chartFrameField_eventuallyEq (I := I) p m).and
      (eventually_all.mpr fun m => hγev m)).and
      ((chartAt H p).open_source.eventually_mem (mem_chart_source H p)))
  have hUsub : U ⊆ (chartAt H p).source := fun q hq => (hU q hq).2
  have hUframe : ∀ m, ∀ q ∈ U,
      ⇑(chartFrameField (I := I) p m) q = chartBasisVecFiber (I := I) p m q :=
    fun m q hq => (hU q hq).1.1 m
  have hUγ : ∀ m, ∀ q ∈ U, γ m q = Γ m q := fun m q hq => (hU q hq).1.2 m
  -- `∇_{∂_j}∂_k = Σ_m γ_m • F_m` on `U`
  have hEqOn : Set.EqOn
      ((g.leviCivita).toAffineConnection.covField
        (⇑(chartFrameField (I := I) p j)) (⇑(chartFrameField (I := I) p k)))
      (fun q => ∑ m, γ m q • ⇑(chartFrameField (I := I) p m) q) U := by
    intro q hq
    have hqsrc : q ∈ (chartAt H p).source := hUsub hq
    have hev : ∀ m, ⇑(chartFrameField (I := I) p m)
        =ᶠ[nhds q] fun x => chartBasisVecFiber (I := I) p m x := fun m =>
      eventuallyEq_of_mem (hUopen.mem_nhds hq) fun x hx => hUframe m x hx
    show (g.leviCivita).cov q (⇑(chartFrameField (I := I) p j) q)
        (⇑(chartFrameField (I := I) p k)) = _
    rw [hUframe j q hq,
      leviCivita_cov_chartFrameField_expansion (I := I) g p j k hqsrc hev]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hUγ m q hq, hUframe m q hq]
  -- locality of the connection
  have hloc := connection_local_openSet (g.leviCivita).toAffineConnection
    (chartBasisVecFiber (I := I) p i p) hcovjk hW hUopen hpU hEqOn
  rw [hloc, AffineConnection.cov_finsetSum_smul_field _ p _ Finset.univ γ _
    hγsmooth (fun m => (chartFrameField (I := I) p m).smooth)]
  -- rewrite each summand
  have hstep : ∀ m : Fin (Module.finrank ℝ E),
      dirTangent (γ m) (chartBasisVecFiber (I := I) p i p) •
          ⇑(chartFrameField (I := I) p m) p
        + γ m p • (g.leviCivita).toAffineConnection.cov p
            (chartBasisVecFiber (I := I) p i p) (⇑(chartFrameField (I := I) p m))
      = partialDeriv (E := E) i (chartChristoffel (I := I) g p j k m)
            (extChartAt I p p) • chartBasisVecFiber (I := I) p m p
        + christoffelSymbolsSecondKind g p j k m •
            ∑ l, christoffelSymbolsSecondKind g p i m l •
              chartBasisVecFiber (I := I) p l p := by
    intro m
    have hd : dirTangent (γ m) (chartBasisVecFiber (I := I) p i p)
        = partialDeriv (E := E) i (chartChristoffel (I := I) g p j k m)
            (extChartAt I p p) := by
      show mfderiv I 𝓘(ℝ) (γ m) p (chartBasisVecFiber (I := I) p i p) = _
      rw [(hγev m).mfderiv_eq]
      exact mfderiv_chartChristoffel_eq_partialDeriv (I := I) g p j k m i
        (mem_chart_source H p)
    have hval : γ m p = christoffelSymbolsSecondKind g p j k m := by
      rw [(hγev m).self_of_nhds, hΓ, christoffelSymbols_metric_formula]
    have hcov : (g.leviCivita).toAffineConnection.cov p
          (chartBasisVecFiber (I := I) p i p) (⇑(chartFrameField (I := I) p m))
        = ∑ l, christoffelSymbolsSecondKind g p i m l •
            chartBasisVecFiber (I := I) p l p := by
      rw [leviCivita_cov_chartFrameField_expansion (I := I) g p i m
        (mem_chart_source H p) (fun b => chartFrameField_eventuallyEq (I := I) p b)]
      exact Finset.sum_congr rfl fun l _ => by rw [christoffelSymbols_metric_formula]
    rw [hd, hval, hcov, chartFrameField_apply_self (I := I) p m]
  rw [Finset.sum_congr rfl fun m _ => hstep m]
  -- reorganize the finite sums
  calc ∑ m, (partialDeriv (E := E) i (chartChristoffel (I := I) g p j k m)
            (extChartAt I p p) • chartBasisVecFiber (I := I) p m p
          + christoffelSymbolsSecondKind g p j k m •
              ∑ l, christoffelSymbolsSecondKind g p i m l •
                chartBasisVecFiber (I := I) p l p)
      = ∑ m, partialDeriv (E := E) i (chartChristoffel (I := I) g p j k m)
            (extChartAt I p p) • chartBasisVecFiber (I := I) p m p
        + ∑ m, ∑ l, (christoffelSymbolsSecondKind g p j k m *
              christoffelSymbolsSecondKind g p i m l) •
            chartBasisVecFiber (I := I) p l p := by
        rw [Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun l _ => smul_smul ..
    _ = ∑ l, partialDeriv (E := E) i (chartChristoffel (I := I) g p j k l)
            (extChartAt I p p) • chartBasisVecFiber (I := I) p l p
        + ∑ l, (∑ s, christoffelSymbolsSecondKind g p j k s *
              christoffelSymbolsSecondKind g p i s l) •
            chartBasisVecFiber (I := I) p l p := by
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => (Finset.sum_smul).symm
    _ = ∑ l, (partialDeriv (E := E) i (chartChristoffel (I := I) g p j k l)
            (extChartAt I p p)
          + ∑ s, christoffelSymbolsSecondKind g p j k s *
              christoffelSymbolsSecondKind g p i s l)
          • chartBasisVecFiber (I := I) p l p := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => (add_smul ..).symm

/-- **Math.** **Prop. — the curvature tensor in local coordinates** (Petersen
§3.1.6, prop:pet-ch3-curvature-coordinate-formula). In the chart frame
`∂_i = chartBasisVecFiber p i` at `p`, writing
`R(∂_i, ∂_j)∂_k = R^l_{ijk} ∂_l`, the coefficients are
`R^l_{ijk} = ∂_i Γ^l_{jk} − ∂_j Γ^l_{ik} + Γ^s_{jk} Γ^l_{is} − Γ^s_{ik} Γ^l_{js}`,
where `Γ^k_{ij} = christoffelSymbolsSecondKind g p i j k` are the Christoffel
symbols at `p` and `∂_i Γ^l_{jk}` is the chart partial derivative
`partialDeriv i (chartChristoffel g p j k l)` of the coordinate Christoffel
function of the fixed chart at `p`, evaluated at the chart image of `p`.

Proof: Petersen's direct expansion. `[∂_i, ∂_j] = 0` kills the bracket term;
near `p` the field `∇_{∂_j}∂_k` equals the frame combination `Γ^s_{jk} ∂_s`
(`leviCivita_cov_chartFrameField_expansion` + locality), and the Leibniz rule
differentiates it along `∂_i` (`leviCivita_cov_cov_chartFrameField`). -/
theorem curvatureTensor_coordinates
    (i j k : Fin (Module.finrank ℝ E)) :
    curvatureTensorAt (g.leviCivita).toAffineConnection p
        (chartBasisVecFiber (I := I) p i p) (chartBasisVecFiber (I := I) p j p)
        (chartBasisVecFiber (I := I) p k p)
      = ∑ l, (partialDeriv (E := E) i (chartChristoffel (I := I) g p j k l)
              (extChartAt I p p)
            - partialDeriv (E := E) j (chartChristoffel (I := I) g p i k l)
              (extChartAt I p p)
            + ∑ s, (christoffelSymbolsSecondKind g p j k s *
                  christoffelSymbolsSecondKind g p i s l
                - christoffelSymbolsSecondKind g p i k s *
                  christoffelSymbolsSecondKind g p j s l))
          • chartBasisVecFiber (I := I) p l p := by
  classical
  -- pass from the pointwise tensor to the global frame fields
  have hA : curvatureTensorAt (g.leviCivita).toAffineConnection p
      (chartBasisVecFiber (I := I) p i p) (chartBasisVecFiber (I := I) p j p)
      (chartBasisVecFiber (I := I) p k p)
      = curvatureTensor (g.leviCivita).toAffineConnection
          (⇑(chartFrameField (I := I) p i)) (⇑(chartFrameField (I := I) p j))
          (⇑(chartFrameField (I := I) p k)) p := by
    rw [← chartFrameField_apply_self (I := I) p i,
      ← chartFrameField_apply_self (I := I) p j,
      ← chartFrameField_apply_self (I := I) p k]
    exact curvatureTensorAt_apply _ (chartFrameField (I := I) p i).smooth
      (chartFrameField (I := I) p j).smooth
      (chartFrameField (I := I) p k).smooth p
  rw [hA, curvatureTensor_apply]
  -- the bracket term vanishes: `[∂_i, ∂_j]|_p = 0`
  have hbr0 : lieDerivativeVectorField I (⇑(chartFrameField (I := I) p i))
      (⇑(chartFrameField (I := I) p j)) p = 0 := by
    rw [lieDerivativeVectorField_eq_mlieBracket,
      Filter.EventuallyEq.mlieBracket_vectorField_eq
        (chartFrameField_eventuallyEq (I := I) p i)
        (chartFrameField_eventuallyEq (I := I) p j)]
    exact mlieBracket_chartBasisVecFiber_eq_zero (I := I) p i j (mem_chart_source H p)
  rw [hbr0, AffineConnection.cov_zero_direction, sub_zero,
    chartFrameField_apply_self (I := I) p i, chartFrameField_apply_self (I := I) p j,
    leviCivita_cov_cov_chartFrameField (I := I) g p i j k,
    leviCivita_cov_cov_chartFrameField (I := I) g p j i k,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← sub_smul]
  congr 1
  rw [Finset.sum_sub_distrib]
  ring

/-- **Math.** **Remark 3.1.8 — lowering the last index of `R^l_{ijk}`**
(Petersen §3.1.6, `rem:pet-ch3-curvature-index-conventions`). Consistently with
`R(X,Y,Z,W) = g(R(X,Y)Z, W)`, the fully lower-index curvature components are
`R_{ijkl} = g_{sl} R^s_{ijk} = R(∂_i, ∂_j, ∂_k, ∂_l)`. Here the left-hand side
is the `(0,4)`-tensor `g(R(∂_i,∂_j)∂_k, ∂_l)` and the coefficients `R^s_{ijk}`
are those of `curvatureTensor_coordinates`; the identity is obtained by pairing
the coordinate expansion `R(∂_i,∂_j)∂_k = R^s_{ijk} ∂_s` against `∂_l` with the
metric, using bilinearity of `g` over the frame sum (so `g_{sl} = g(∂_s, ∂_l)`). -/
theorem curvatureTensor_indexLowering
    (i j k l : Fin (Module.finrank ℝ E)) :
    g.metricInner p
        (curvatureTensorAt (g.leviCivita).toAffineConnection p
          (chartBasisVecFiber (I := I) p i p) (chartBasisVecFiber (I := I) p j p)
          (chartBasisVecFiber (I := I) p k p))
        (chartBasisVecFiber (I := I) p l p)
      = ∑ s, (partialDeriv (E := E) i (chartChristoffel (I := I) g p j k s)
                (extChartAt I p p)
            - partialDeriv (E := E) j (chartChristoffel (I := I) g p i k s)
                (extChartAt I p p)
            + ∑ t, (christoffelSymbolsSecondKind g p j k t *
                  christoffelSymbolsSecondKind g p i t s
                - christoffelSymbolsSecondKind g p i k t *
                  christoffelSymbolsSecondKind g p j t s))
          * g.metricInner p (chartBasisVecFiber (I := I) p s p)
              (chartBasisVecFiber (I := I) p l p) := by
  rw [curvatureTensor_coordinates]
  exact metricInner_sum_smul_left g p _ _ _

end CurvatureCoordinates

end PetersenLib

end
