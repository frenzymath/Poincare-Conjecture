import PetersenLib.Ch02.Connections
import PetersenLib.Ch02.CovariantDerivative
import OpenGALib.Riemannian.Connection.ChartFrameBridge

/-!
# Petersen Ch. 2, §2.4 — The Connection in Tensor Notation

The coordinate expressions of Petersen §2.4, read against the chart frame
`∂_i = chartBasisVecFiber α i` of the chart at `α`:

* `metricCoordinateFormulas` — the metric components `g_{ij} = g(∂_i, ∂_j)` are
  the chart Gram matrix, and `g^{ik}g_{kj} = δ^i_j`
  (def:pet-ch2-metric-coordinate-formulas);
* `vectorDualToForm` — the vector field `X = g^{ij}ω_j ∂_i` dual to a 1-form
  `ω`, agreeing with the metric Riesz dual (def:pet-ch2-vector-dual-to-form);
* `gradient_coordinate_formula` — `∇f = g^{ij}(∂_j f)∂_i`
  (rem:pet-ch2-gradient-coordinate-formula);
* `christoffelSymbolsSecondKind` — `Γ^k_{ij}` defined by
  `∇_{∂_i}∂_j = Γ^k_{ij}∂_k` (def:pet-ch2-christoffel-symbols-second-kind);
* `christoffelSymbols_metric_formula` —
  `Γ^k_{ij} = ½ g^{kl}(∂_i g_{lj} + ∂_j g_{li} − ∂_l g_{ij})`
  (prop:pet-ch2-christoffel-formula);
* `christoffelSymbolsFirstKind` — `Γ_{ij,k}` with
  `Γ_{ij,k} = g(∇_{∂_i}∂_j, ∂_k)` (def:pet-ch2-christoffel-symbols-first-kind);
* `christoffel_symmetric_metric_property` — `Γ^k_{ij} = Γ^k_{ji}` and
  `∂_k g_{ij} = Γ_{ki,j} + Γ_{kj,i}`
  (prop:pet-ch2-christoffel-symmetry-metric-property).

## Design notes

* The chapter's Levi-Civita connection `g.leviCivita` differentiates *global*
  smooth fields, while the chart frame `chartBasisVecFiber p j` is smooth only
  on the chart base set. Following Petersen's implicit convention that all
  computations are local, `chartFrameExtension p j` fixes a global smooth field
  agreeing with `∂_j` near `p` (`exists_smoothVectorField_eventuallyEq`);
  locality of connections (Lem. 2.2.3, `connection_local_openSet`) makes the
  Christoffel symbols independent of this choice
  (`leviCivita_cov_chartFrame_congr`).
* The metric formula for `Γ^k_{ij}` is Koszul's formula
  (`RiemannianConnection.koszul`) evaluated on the frame: the brackets vanish
  (`mlieBracket_chartBasisVecFiber_eq_zero`, transported through the germ of
  the extension) and the directional derivatives of the metric become chart
  partial derivatives of the Gram matrix
  (`mfderiv_chartGramMatrix_eq_partialDeriv`); the resulting linear system is
  solved through the inverse Gram matrix exactly as in the vendored
  `christoffel_bridge_inner`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.4.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff Matrix

namespace PetersenLib

open Riemannian Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## §2.4: coordinate formulas for the metric -/

/-- **Math.** **Coordinate formulas for the metric** (Petersen §2.4,
def:pet-ch2-metric-coordinate-formulas). In the chart at `α`, the components
of the metric on the coordinate frame `∂_i = chartBasisVecFiber α i` are the
chart Gram matrix, `g(∂_i, ∂_j) = g_{ij}`, and the inverse matrix `[g^{ij}]`
satisfies `g^{ik}g_{kj} = δ^i_j` on the chart base set. -/
theorem metricCoordinateFormulas (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    g.metricInner x (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x)
      = chartGramMatrix (I := I) g α x i j
    ∧ chartInvGramMatrix (I := I) g α x * chartGramMatrix (I := I) g α x = 1 :=
  ⟨rfl, chartInvGramMatrix_mul_chartGramMatrix (I := I) g α hx⟩

/-- **Eng.** Bilinear expansion of the metric against a linear combination in
its first slot: `g(Σ c_m • w_m, v) = Σ c_m g(w_m, v)`. -/
private theorem metricInner_sum_smul_left (g : RiemannianMetric I M) (x : M)
    {n : ℕ} (c : Fin n → ℝ) (w : Fin n → TangentSpace I x) (v : TangentSpace I x) :
    g.metricInner x (∑ m, c m • w m) v = ∑ m, c m * g.metricInner x (w m) v := by
  show (g.inner x) (∑ m, c m • w m) v = _
  rw [map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

/-- **Eng.** Bilinear expansion of the metric against a linear combination in
its second slot: `g(v, Σ c_m • w_m) = Σ c_m g(v, w_m)`. -/
private theorem metricInner_sum_smul_right (g : RiemannianMetric I M) (x : M)
    {n : ℕ} (v : TangentSpace I x) (c : Fin n → ℝ) (w : Fin n → TangentSpace I x) :
    g.metricInner x v (∑ m, c m • w m) = ∑ m, c m * g.metricInner x v (w m) := by
  show (g.inner x v) (∑ m, c m • w m) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

/-- **Math.** The **vector field dual to a 1-form** (Petersen §2.4,
def:pet-ch2-vector-dual-to-form): in the chart at `α`, the vector
`X = g^{ij}ω_j ∂_i` associated to a covector `φ` — the chart-coordinate
realization of the implicit definition `g(X, Y) = φ(Y)`
(`vectorDualToForm_eq_metricRiesz`). -/
def vectorDualToForm (g : RiemannianMetric I M) (α : M) (x : M)
    (φ : TangentSpace I x →L[ℝ] ℝ) : TangentSpace I x :=
  ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
      φ (chartBasisVecFiber (I := I) α j x)) •
    chartBasisVecFiber (I := I) α i x

/-- **Math.** Petersen's verification that `X = g^{ij}ω_j ∂_i` satisfies
`g(X, ∂_k) = ω_k`, tested against the coordinate frame: multiplying
`g_{ij}X^i = ω_j` by `g^{kj}` and using the symmetry of `g_{ij}` together with
`g^{ik}g_{kj} = δ^i_j`. -/
private theorem vectorDualToForm_inner_chartBasis (g : RiemannianMetric I M)
    (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (φ : TangentSpace I x →L[ℝ] ℝ) (k : Fin (Module.finrank ℝ E)) :
    g.metricInner x (vectorDualToForm g α x φ) (chartBasisVecFiber (I := I) α k x)
      = φ (chartBasisVecFiber (I := I) α k x) := by
  classical
  rw [vectorDualToForm, metricInner_sum_smul_left]
  have hstep : ∀ i : Fin (Module.finrank ℝ E),
      (∑ j, chartInvGramMatrix (I := I) g α x i j *
          φ (chartBasisVecFiber (I := I) α j x))
        * g.metricInner x (chartBasisVecFiber (I := I) α i x)
            (chartBasisVecFiber (I := I) α k x)
      = ∑ j, chartGramMatrix (I := I) g α x k i *
          chartInvGramMatrix (I := I) g α x i j *
          φ (chartBasisVecFiber (I := I) α j x) := by
    intro i
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsym : g.metricInner x (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α k x)
        = chartGramMatrix (I := I) g α x k i := g.metricInner_comm x _ _
    rw [hsym]
    ring
  rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_comm]
  have hrow : ∀ j : Fin (Module.finrank ℝ E),
      (∑ i, chartGramMatrix (I := I) g α x k i *
          chartInvGramMatrix (I := I) g α x i j *
          φ (chartBasisVecFiber (I := I) α j x))
      = (if k = j then (1 : ℝ) else 0) * φ (chartBasisVecFiber (I := I) α j x) := by
    intro j
    rw [← Finset.sum_mul]
    congr 1
    have hmul : ∑ i, chartGramMatrix (I := I) g α x k i *
        chartInvGramMatrix (I := I) g α x i j
        = (chartGramMatrix (I := I) g α x * chartInvGramMatrix (I := I) g α x) k j :=
      (Matrix.mul_apply).symm
    rw [hmul, chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hx,
      Matrix.one_apply]
  rw [Finset.sum_congr rfl fun j _ => hrow j]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **Math.** The chart-coordinate dual vector field agrees with the metric
Riesz dual: `g^{ij}ω_j ∂_i` is *the* vector `X` with `g(X, Y) = ω(Y)` for all
`Y` (Petersen §2.4, def:pet-ch2-vector-dual-to-form). Proof: test against the
chart basis (`vectorDualToForm_inner_chartBasis`) and expand an arbitrary
tangent vector in the chart-basis family. -/
theorem vectorDualToForm_eq_metricRiesz (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (φ : TangentSpace I x →L[ℝ] ℝ) :
    vectorDualToForm g α x φ = g.metricRiesz x φ := by
  classical
  refine g.metricRiesz_unique x _ φ fun w => ?_
  have hw : w = ∑ m, ((chartBasisFamily (I := I) α hx).repr w m) •
      chartBasisVecFiber (I := I) α m x := by
    conv_lhs => rw [← (chartBasisFamily (I := I) α hx).sum_repr w]
    exact Finset.sum_congr rfl fun m _ => by rw [chartBasisFamily_apply]
  rw [hw, metricInner_sum_smul_right, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [vectorDualToForm_inner_chartBasis (I := I) g α hx φ m, map_smul, smul_eq_mul]

/-- **Math.** The **gradient in coordinates** (Petersen §2.4,
rem:pet-ch2-gradient-coordinate-formula): `∇f = g^{ij}(∂_j f)∂_i` — the
dual-vector-field formula applied to the 1-form `ω = df`. -/
theorem gradient_coordinate_formula (g : RiemannianMetric I M) (α : M)
    (f : M → ℝ) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    gradient g f x
      = ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
            directionalDerivative (chartBasisVecFiber (I := I) α j) f x) •
          chartBasisVecFiber (I := I) α i x := by
  rw [show gradient g f x = g.metricRiesz x (mfderiv I 𝓘(ℝ) f x) from rfl,
    ← vectorDualToForm_eq_metricRiesz (I := I) g α hx]
  rfl

/-! ## §2.4: the Christoffel symbols -/

/-- **Eng.** Symmetry of the chart Gram entries passed through the chart
partial derivative: `∂_r G_{ab} = ∂_r G_{ba}`. -/
private theorem partialDeriv_chartGramOnE_symm (g : RiemannianMetric I M)
    (α : M) (a b r : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) r (chartGramOnE (I := I) g α a b) y
      = partialDeriv (E := E) r (chartGramOnE (I := I) g α b a) y := by
  unfold partialDeriv
  rw [show chartGramOnE (I := I) g α a b = chartGramOnE (I := I) g α b a from
    funext fun z => chartGramOnE_symm (I := I) g α a b z]

/-- **Math.** The **Christoffel symbols of the first kind** (Petersen §2.4,
def:pet-ch2-christoffel-symbols-first-kind), classically `[ij, k]`:
`Γ_{ij,k} := ½(∂_j g_{ik} + ∂_i g_{jk} − ∂_k g_{ij})`, read in the chart at
`p` (the partial derivatives are those of the chart Gram matrix, evaluated at
the chart image of `p`). The identity `Γ_{ij,k} = g(∇_{∂_i}∂_j, ∂_k)` is
`christoffelSymbolsFirstKind_eq_metricInner_cov`. -/
def christoffelSymbolsFirstKind (g : RiemannianMetric I M) (p : M)
    (i j k : Fin (Module.finrank ℝ E)) : ℝ :=
  (1 / 2 : ℝ) *
    (partialDeriv (E := E) j (chartGramOnE (I := I) g p i k) (extChartAt I p p)
      + partialDeriv (E := E) i (chartGramOnE (I := I) g p j k) (extChartAt I p p)
      - partialDeriv (E := E) k (chartGramOnE (I := I) g p i j) (extChartAt I p p))

section ChristoffelSymbols

variable [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- **Eng.** A global smooth vector field agreeing with the coordinate frame
field `∂_j = chartBasisVecFiber p j` on a neighborhood of `p`
(`exists_smoothVectorField_eventuallyEq`), so that the chapter's connection —
which differentiates global smooth fields — can be evaluated on the frame.
The choice is irrelevant near `p` (`leviCivita_cov_chartFrame_congr`). -/
private def chartFrameExtension (p : M) (j : Fin (Module.finrank ℝ E)) :
    SmoothVectorField I M :=
  (exists_smoothVectorField_eventuallyEq (I := I)
    (σ := fun q => chartBasisVecFiber (I := I) p j q)
    (trivializationAt E (TangentSpace I) p).open_baseSet
    (chartBasisVec_contMDiffOn (I := I) p j)
    (FiberBundle.mem_baseSet_trivializationAt' p)).choose

/-- **Eng.** The defining property of `chartFrameExtension`: it agrees with the
coordinate frame field near `p`. -/
private theorem chartFrameExtension_eventuallyEq (p : M)
    (j : Fin (Module.finrank ℝ E)) :
    ⇑(chartFrameExtension (I := I) p j)
      =ᶠ[nhds p] fun q => chartBasisVecFiber (I := I) p j q :=
  (exists_smoothVectorField_eventuallyEq (I := I)
    (σ := fun q => chartBasisVecFiber (I := I) p j q)
    (trivializationAt E (TangentSpace I) p).open_baseSet
    (chartBasisVec_contMDiffOn (I := I) p j)
    (FiberBundle.mem_baseSet_trivializationAt' p)).choose_spec

private theorem chartFrameExtension_apply_self (p : M)
    (j : Fin (Module.finrank ℝ E)) :
    chartFrameExtension (I := I) p j p = chartBasisVecFiber (I := I) p j p :=
  (chartFrameExtension_eventuallyEq (I := I) p j).self_of_nhds

/-- **Math.** Locality of the Levi-Civita connection on the frame extension
(Petersen Lem. 2.2.3): differentiating *any* global smooth field agreeing with
the coordinate frame field `∂_j` near `p` gives the same covariant derivative
at `p` — the Christoffel symbols do not depend on the choice of extension. -/
theorem leviCivita_cov_chartFrame_congr (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (j : Fin (Module.finrank ℝ E))
    {Z : Π x : M, TangentSpace I x} (hZ : IsSmoothVectorField Z)
    (hZev : ∀ᶠ q in nhds p, Z q = chartBasisVecFiber (I := I) p j q) :
    (g.leviCivita).cov p v Z
      = (g.leviCivita).cov p v (⇑(chartFrameExtension (I := I) p j)) := by
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨U, hU, hUopen, hpU⟩ :=
    eventually_nhds_iff.mp (hZev.and (chartFrameExtension_eventuallyEq (I := I) p j))
  exact connection_local_openSet (g.leviCivita).toAffineConnection v hZ
    (chartFrameExtension (I := I) p j).smooth hUopen hpU
    (fun q hq => ((hU q hq).1).trans ((hU q hq).2).symm)

/-- **Math.** The **Christoffel symbols of the second kind** `Γ^k_{ij}`
(Petersen §2.4, def:pet-ch2-christoffel-symbols-second-kind): the coefficients
of the covariant derivative of the coordinate frame in the coordinate frame,
`∇_{∂_i}∂_j = Γ^k_{ij}∂_k` — here the `k`-th coordinate of
`∇_{∂_i|_p}∂_j ∈ T_pM` in the chart-basis family at `p`, with `∂_j` fed to the
connection through a global smooth extension of its germ at `p`
(`chartFrameExtension`; the choice is irrelevant by
`leviCivita_cov_chartFrame_congr`). -/
def christoffelSymbolsSecondKind (g : RiemannianMetric I M) (p : M)
    (i j k : Fin (Module.finrank ℝ E)) : ℝ :=
  (chartBasisFamily (I := I) p (FiberBundle.mem_baseSet_trivializationAt' p)).repr
    ((g.leviCivita).cov p (chartBasisVecFiber (I := I) p i p)
      (⇑(chartFrameExtension (I := I) p j))) k

/-- **Math.** The frame extensions have **vanishing pairwise Lie brackets** at
`p`: the bracket only sees germs, so it agrees with the bracket of the
coordinate frame fields, which vanishes (`[∂_a, ∂_b] = 0`,
`mlieBracket_chartBasisVecFiber_eq_zero`). -/
private theorem lieDerivative_chartFrameExtension_eq_zero (p : M)
    (a b : Fin (Module.finrank ℝ E)) :
    lieDerivativeVectorField I (⇑(chartFrameExtension (I := I) p a))
      (⇑(chartFrameExtension (I := I) p b)) p = 0 := by
  rw [lieDerivativeVectorField_eq_mlieBracket,
    Filter.EventuallyEq.mlieBracket_vectorField_eq
      (chartFrameExtension_eventuallyEq (I := I) p a)
      (chartFrameExtension_eventuallyEq (I := I) p b)]
  exact mlieBracket_chartBasisVecFiber_eq_zero (I := I) p a b (mem_chart_source H p)

/-- **Math.** The directional derivative of the metric components along the
frame extensions is the **chart partial derivative of the Gram matrix**:
`∂_r⟨∂_a, ∂_b⟩ = ∂_r G_{ab}` — `mfderiv` only sees germs, so the frame
extensions can be replaced by the frame fields, whose Gram function is the
chart Gram entry (`mfderiv_chartGramMatrix_eq_partialDeriv`). -/
private theorem directionalDerivative_chartFrameExtension_metric
    (g : RiemannianMetric I M) (p : M) (r a b : Fin (Module.finrank ℝ E)) :
    directionalDerivative (⇑(chartFrameExtension (I := I) p r))
      (fun q => g.metricInner q (chartFrameExtension (I := I) p a q)
        (chartFrameExtension (I := I) p b q)) p
      = partialDeriv (E := E) r (chartGramOnE (I := I) g p a b) (extChartAt I p p) := by
  have hev : (fun q => g.metricInner q (chartFrameExtension (I := I) p a q)
      (chartFrameExtension (I := I) p b q))
      =ᶠ[nhds p] fun q => chartGramMatrix (I := I) g p q a b := by
    filter_upwards [chartFrameExtension_eventuallyEq (I := I) p a,
      chartFrameExtension_eventuallyEq (I := I) p b] with q hqa hqb
    rw [hqa, hqb]
    rfl
  rw [directionalDerivative_apply, hev.mfderiv_eq,
    chartFrameExtension_apply_self (I := I) p r]
  exact mfderiv_chartGramMatrix_eq_partialDeriv (I := I) g p a b r
    (mem_chart_source H p)

/-- **Math.** **Koszul's formula collapsed on the coordinate frame** (the
computational heart of prop:pet-ch2-christoffel-formula): with vanishing
brackets and Gram partial derivatives,
`2 g(∇_{∂_i}∂_j, ∂_l) = ∂_i g_{lj} + ∂_j g_{li} − ∂_l g_{ij}`. -/
private theorem koszul_chartFrame_collapse (g : RiemannianMetric I M) (p : M)
    (i j l : Fin (Module.finrank ℝ E)) :
    2 * g.metricInner p
        ((g.leviCivita).cov p (chartBasisVecFiber (I := I) p i p)
          (⇑(chartFrameExtension (I := I) p j)))
        (chartBasisVecFiber (I := I) p l p)
      = partialDeriv (E := E) i (chartGramOnE (I := I) g p l j) (extChartAt I p p)
        + partialDeriv (E := E) j (chartGramOnE (I := I) g p l i) (extChartAt I p p)
        - partialDeriv (E := E) l (chartGramOnE (I := I) g p i j) (extChartAt I p p) := by
  have hsmi : IsSmoothVectorField
      (⇑(chartFrameExtension (I := I) p i) : Π x : M, TangentSpace I x) :=
    (chartFrameExtension (I := I) p i).smooth
  have hsmj : IsSmoothVectorField
      (⇑(chartFrameExtension (I := I) p j) : Π x : M, TangentSpace I x) :=
    (chartFrameExtension (I := I) p j).smooth
  have hsml : IsSmoothVectorField
      (⇑(chartFrameExtension (I := I) p l) : Π x : M, TangentSpace I x) :=
    (chartFrameExtension (I := I) p l).smooth
  -- Koszul's formula with `X = ∂_j`, `Y = ∂_i`, `Z = ∂_l` (extensions).
  have hK := (g.leviCivita).koszul hsmj hsmi hsml p
  unfold koszulExpression at hK
  -- The three bracket terms vanish.
  rw [lieDerivative_chartFrameExtension_eq_zero (I := I) p j i,
    lieDerivative_chartFrameExtension_eq_zero (I := I) p i l,
    lieDerivative_chartFrameExtension_eq_zero (I := I) p l j,
    g.metricInner_zero_left, g.metricInner_zero_left, g.metricInner_zero_left] at hK
  -- The three directional derivatives become Gram partial derivatives.
  rw [directionalDerivative_chartFrameExtension_metric (I := I) g p j i l,
    directionalDerivative_chartFrameExtension_metric (I := I) g p i j l,
    directionalDerivative_chartFrameExtension_metric (I := I) g p l j i] at hK
  -- Evaluate the extensions at `p`.
  rw [chartFrameExtension_apply_self (I := I) p i,
    chartFrameExtension_apply_self (I := I) p l] at hK
  have s1 := partialDeriv_chartGramOnE_symm (I := I) g p i l j (extChartAt I p p)
  have s2 := partialDeriv_chartGramOnE_symm (I := I) g p j l i (extChartAt I p p)
  have s3 := partialDeriv_chartGramOnE_symm (I := I) g p j i l (extChartAt I p p)
  linarith [hK, s1, s2, s3]

/-- **Math.** The **inner form** of the Christoffel formula: contracting with
the Gram matrix, `g(∇_{∂_i}∂_j, ∂_l) = Σ_m g_{lm} Γ^m_{ij}` where `Γ^m_{ij}` is
the chart-coordinate metric formula `chartChristoffel`. -/
private theorem metricInner_cov_chartFrame (g : RiemannianMetric I M) (p : M)
    (i j l : Fin (Module.finrank ℝ E)) :
    g.metricInner p
        ((g.leviCivita).cov p (chartBasisVecFiber (I := I) p i p)
          (⇑(chartFrameExtension (I := I) p j)))
        (chartBasisVecFiber (I := I) p l p)
      = ∑ m, chartGramOnE (I := I) g p l m (extChartAt I p p)
          * chartChristoffel (I := I) g p i j m (extChartAt I p p) := by
  have hpe : (extChartAt I p).symm (extChartAt I p p) = p := extChartAt_to_inv p
  have hy : (extChartAt I p).symm (extChartAt I p p)
      ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [hpe]
    exact FiberBundle.mem_baseSet_trivializationAt' p
  have hc := chartGram_christoffel_contraction (I := I) g p l i j
    (extChartAt I p p) hy
  have hk := koszul_chartFrame_collapse (I := I) g p i j l
  linarith

/-- **Math.** **Prop. — the Christoffel symbols in terms of the metric**
(Petersen §2.4, prop:pet-ch2-christoffel-formula):
`Γ^k_{ij} = ½ g^{kl}(∂_i g_{lj} + ∂_j g_{li} − ∂_l g_{ij})`, i.e. the abstract
symbols defined by `∇_{∂_i}∂_j = Γ^k_{ij}∂_k` coincide with the chart-coordinate
metric formula `chartChristoffel`, evaluated at the chart image of `p`.
Proof: Koszul's formula on the frame (`koszul_chartFrame_collapse`), contracted
through the inverse Gram matrix (`chartGram_christoffel_contraction`) and read
off in the chart-basis family by non-degeneracy of the metric. -/
theorem christoffelSymbols_metric_formula (g : RiemannianMetric I M) (p : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    christoffelSymbolsSecondKind g p i j k
      = chartChristoffel (I := I) g p i j k (extChartAt I p p) := by
  classical
  have hb : p ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' p
  have hpe : (extChartAt I p).symm (extChartAt I p p) = p := extChartAt_to_inv p
  have hgram : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g p a b (extChartAt I p p)
        = g.metricInner p (chartBasisVecFiber (I := I) p a p)
            (chartBasisVecFiber (I := I) p b p) := by
    intro a b
    rw [chartGramOnE_def, hpe]
    rfl
  -- The vector form: `∇_{∂_i}∂_j = Σ_m Γ^m_{ij} ∂_m` at `p`.
  have hvec : (g.leviCivita).cov p (chartBasisVecFiber (I := I) p i p)
      (⇑(chartFrameExtension (I := I) p j))
      = ∑ m, chartChristoffel (I := I) g p i j m (extChartAt I p p) •
          chartBasisVecFiber (I := I) p m p := by
    refine (g.metricInner_eq_iff_eq p _ _).mp fun Z => ?_
    have key : ∀ m : Fin (Module.finrank ℝ E),
        g.metricInner p ((g.leviCivita).cov p (chartBasisVecFiber (I := I) p i p)
            (⇑(chartFrameExtension (I := I) p j)))
          (chartBasisVecFiber (I := I) p m p)
        = g.metricInner p
            (∑ a, chartChristoffel (I := I) g p i j a (extChartAt I p p) •
              chartBasisVecFiber (I := I) p a p)
            (chartBasisVecFiber (I := I) p m p) := by
      intro m
      rw [metricInner_cov_chartFrame (I := I) g p i j m, metricInner_sum_smul_left]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hgram m a, mul_comm]
      congr 1
      exact g.metricInner_comm p _ _
    have hZ : Z = ∑ m, ((chartBasisFamily (I := I) p hb).repr Z m) •
        chartBasisVecFiber (I := I) p m p := by
      conv_lhs => rw [← (chartBasisFamily (I := I) p hb).sum_repr Z]
      exact Finset.sum_congr rfl fun m _ => by rw [chartBasisFamily_apply]
    rw [hZ, metricInner_sum_smul_right, metricInner_sum_smul_right]
    exact Finset.sum_congr rfl fun m _ => by rw [key m]
  -- Read off the `k`-th coordinate.
  show (chartBasisFamily (I := I) p hb).repr
      ((g.leviCivita).cov p (chartBasisVecFiber (I := I) p i p)
        (⇑(chartFrameExtension (I := I) p j))) k = _
  rw [hvec, show (∑ m, chartChristoffel (I := I) g p i j m (extChartAt I p p) •
      chartBasisVecFiber (I := I) p m p)
      = ∑ m, chartChristoffel (I := I) g p i j m (extChartAt I p p) •
          (chartBasisFamily (I := I) p hb) m from
    Finset.sum_congr rfl fun m _ => by rw [chartBasisFamily_apply],
    Module.Basis.repr_sum_self]

/-- **Math.** The Christoffel symbols of the first kind compute the metric
pairing of the covariant derivative of the frame with the frame (Petersen
§2.4, def:pet-ch2-christoffel-symbols-first-kind):
`Γ_{ij,k} = g(∇_{∂_i}∂_j, ∂_k)` — the Koszul collapse
(`koszul_chartFrame_collapse`) before contracting with the inverse Gram
matrix. -/
theorem christoffelSymbolsFirstKind_eq_metricInner_cov (g : RiemannianMetric I M)
    (p : M) (i j k : Fin (Module.finrank ℝ E)) :
    christoffelSymbolsFirstKind g p i j k
      = g.metricInner p
          ((g.leviCivita).cov p (chartBasisVecFiber (I := I) p i p)
            (⇑(chartFrameExtension (I := I) p j)))
          (chartBasisVecFiber (I := I) p k p) := by
  have hk := koszul_chartFrame_collapse (I := I) g p i j k
  have s1 := partialDeriv_chartGramOnE_symm (I := I) g p i k j (extChartAt I p p)
  have s2 := partialDeriv_chartGramOnE_symm (I := I) g p j k i (extChartAt I p p)
  unfold christoffelSymbolsFirstKind
  linarith [hk, s1, s2]

/-- **Math.** **Torsion-free and metric properties in coordinates** (Petersen
§2.4, prop:pet-ch2-christoffel-symmetry-metric-property). Torsion-freeness of
the Levi-Civita connection is the symmetry `Γ^k_{ij} = Γ^k_{ji}` (since
`[∂_i, ∂_j] = 0`), and the metric property reads
`∂_k g_{ij} = Γ_{ki,j} + Γ_{kj,i}`. -/
theorem christoffel_symmetric_metric_property (g : RiemannianMetric I M) (p : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    christoffelSymbolsSecondKind g p i j k = christoffelSymbolsSecondKind g p j i k
    ∧ partialDeriv (E := E) k (chartGramOnE (I := I) g p i j) (extChartAt I p p)
        = christoffelSymbolsFirstKind g p k i j
          + christoffelSymbolsFirstKind g p k j i := by
  constructor
  · rw [christoffelSymbols_metric_formula, christoffelSymbols_metric_formula]
    exact chartChristoffel_symm (I := I) g p i j k (extChartAt I p p)
  · have s1 := partialDeriv_chartGramOnE_symm (I := I) g p j i k (extChartAt I p p)
    unfold christoffelSymbolsFirstKind
    linarith [s1]

end ChristoffelSymbols

end PetersenLib

end
