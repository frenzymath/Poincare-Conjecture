import PetersenLib.Vendored.OpenGA.Geodesic.CovariantDerivative
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Petersen Ch. 5, §5.1 — Mixed Partials (GTM 171, 3rd ed.)

Petersen characterizes the second partials `∂²c/∂v∂w` of a map `c : Ω → M` by two
properties: **(1)** symmetry in `v, w`, and **(2)** the product rule against the
metric, `∂_z g(∂_v c, ∂_w c) = g(∂²c/∂z∂v, ∂_w c) + g(∂_v c, ∂²c/∂z∂w)`. Together
these force a Koszul-type formula expressing `2 g(∂²c/∂v∂w, ∂_z c)` through first
partials only, whence **uniqueness** (Lemma 5.1.1); the chart-coordinate
Christoffel formula **realizes** both properties (Theorem 5.1.2).

We formalize at chart level: a fixed chart basepoint `α : M`, maps
`c : F → E` into the chart target in the model space `E`, the metric read through
the chart as `chartMetricInner g α` and the Christoffel correction as
`Geodesic.chartChristoffelContraction g α`.

* `PetersenLib.mixedPartialCoord g α c x v w` — the Γ-corrected coordinate mixed
  second partial `∂²c/∂v∂w = D²c(v,w) + Γ(∂_v c, ∂_w c)`.
* `PetersenLib.mixedPartialCoord_symm` — property (1), from Schwarz plus the
  symmetry of the Christoffel contraction.
* `PetersenLib.mixedPartialCoord_productRule` — property (2), directional form,
  from the metric-compatibility engine `hasDerivAt_chartMetricInner_along`.
* `PetersenLib.mixedPartialCoord_koszul` — the six-term Koszul cancellation.
* `PetersenLib.mixedPartials_uniqueness` — **Lemma 5.1.1**: any operator
  satisfying (1) and (2) (stably under Petersen's `c(x) + t·ξ` extensions) agrees
  with `mixedPartialCoord`.
* `PetersenLib.mixedPartials_existence` — **Theorem 5.1.2**: `mixedPartialCoord`
  satisfies (1) and (2).

Reference: Petersen, *Riemannian Geometry*, 3rd ed., §5.1.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff Matrix

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## Elementary properties of the chart metric pairing -/

/-- **Math.** The chart Gram inner product is **symmetric**, inherited from the
symmetry of the Gram matrix `G_{ij} = G_{ji}`. -/
theorem chartMetricInner_symm (g : RiemannianMetric I M) (α : M) (y a b : E) :
    chartMetricInner (I := I) g α y a b = chartMetricInner (I := I) g α y b a := by
  rw [chartMetricInner_def, chartMetricInner_def, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [chartGramOnE_symm (I := I) g α j i]
  ring

/-- **Math.** The chart Gram inner product is additive over differences in its
first vector argument. -/
theorem chartMetricInner_sub_left (g : RiemannianMetric I M) (α : M) (y a a' b : E) :
    chartMetricInner (I := I) g α y (a - a') b
      = chartMetricInner (I := I) g α y a b - chartMetricInner (I := I) g α y a' b := by
  simp only [chartMetricInner_def, Geodesic.chartCoord_def, map_sub, Finsupp.coe_sub,
    Pi.sub_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Math.** **Nondegeneracy of the chart metric pairing** at chart points. If
`y` lies in the chart target and the vector `a` pairs to zero against every
`z : E`, then `a = 0`. This is positive-definiteness of the Gram matrix
(`chartGramMatrix_posDef`) tested on the coordinate vector of `a`: the quadratic
form `⟨a, a⟩_y` is then both zero and strictly positive unless `a = 0`. -/
theorem chartMetricInner_nondegenerate (g : RiemannianMetric I M) (α : M) {y a : E}
    (hy : y ∈ (extChartAt I α).target)
    (h : ∀ z : E, chartMetricInner (I := I) g α y a z = 0) : a = 0 := by
  classical
  by_contra ha
  have hbase : (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source,
      ← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I α).map_target hy
  have hpd : (chartGramMatrix (I := I) g α ((extChartAt I α).symm y)).PosDef :=
    chartGramMatrix_posDef (I := I) g α hbase
  set cvec : Fin (Module.finrank ℝ E) → ℝ := fun i => Geodesic.chartCoord (E := E) i a
    with hcvec
  have hcnz : cvec ≠ 0 := by
    intro hc0
    apply ha
    have hrepr : (Module.finBasis ℝ E).repr a = 0 := by
      ext i
      simpa [hcvec] using congrFun hc0 i
    exact (Module.finBasis ℝ E).repr.map_eq_zero_iff.mp hrepr
  have hpos := hpd.dotProduct_mulVec_pos hcnz
  have heq : star cvec ⬝ᵥ (chartGramMatrix (I := I) g α ((extChartAt I α).symm y) *ᵥ cvec)
      = chartMetricInner (I := I) g α y a a := by
    simp only [chartMetricInner_def, chartGramOnE_def, dotProduct, Matrix.mulVec,
      Pi.star_apply, star_trivial, hcvec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [heq, h a] at hpos
  exact lt_irrefl 0 hpos

/-! ## The chart-coordinate mixed second partial -/

/-- **Math.** Petersen §5.1, the chart-coordinate **mixed second partial**
`∂²c/∂v∂w` of a map `c : F → E` into the chart target at `α`, defined by the
Γ-corrected coordinate formula
$$\frac{\partial^2 c}{\partial v\,\partial w}
  = D\big(y \mapsto Dc(y)\,w\big)(x)\,v + \Gamma\big(Dc(x)\,v, Dc(x)\,w\big)(c(x)),$$
where `Γ` is the chart Christoffel contraction of the metric `g` at the chart
basepoint `α`. This is the coordinate operator that Theorem 5.1.2 shows satisfies
Petersen's two axioms, and Lemma 5.1.1 shows is the unique such operator. -/
def mixedPartialCoord (g : RiemannianMetric I M) (α : M) (c : F → E) (x : F) (v w : F) : E :=
  fderiv ℝ (fun y => fderiv ℝ c y w) x v
    + Geodesic.chartChristoffelContraction (I := I) g α (fderiv ℝ c x v) (fderiv ℝ c x w) (c x)

@[simp] theorem mixedPartialCoord_def (g : RiemannianMetric I M) (α : M)
    (c : F → E) (x : F) (v w : F) :
    mixedPartialCoord (I := I) g α c x v w
      = fderiv ℝ (fun y => fderiv ℝ c y w) x v
        + Geodesic.chartChristoffelContraction (I := I) g α
            (fderiv ℝ c x v) (fderiv ℝ c x w) (c x) := rfl

/-- **Math.** The directional derivative of the slice `y ↦ Dc(y)·w` equals the
second derivative `D²c(x)` applied to the two directions: `D(Dc(·)w)(x)·v =
D²c(x)·v·w`. Pure calculus bookkeeping through `fderiv_clm_apply`. -/
theorem fderiv_fderiv_apply {c : F → E} {x : F}
    (hfd : DifferentiableAt ℝ (fderiv ℝ c) x) (w v : F) :
    fderiv ℝ (fun y => fderiv ℝ c y w) x v = fderiv ℝ (fderiv ℝ c) x v w := by
  rw [fderiv_clm_apply hfd (differentiableAt_const w)]
  simp

/-- **Math.** Petersen §5.1, **property (1)** for the coordinate mixed partial:
`∂²c/∂v∂w = ∂²c/∂w∂v` for a `C²` map. Schwarz symmetry of the second derivative
(`ContDiffAt.isSymmSndFDerivAt`) handles the leading term, and the symmetry of the
Christoffel contraction (`chartChristoffelContraction_symm`) the correction term. -/
theorem mixedPartialCoord_symm (g : RiemannianMetric I M) (α : M) {c : F → E} {x : F}
    (hc : ContDiffAt ℝ 2 c x) (v w : F) :
    mixedPartialCoord (I := I) g α c x v w = mixedPartialCoord (I := I) g α c x w v := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ c) x :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsymm : IsSymmSndFDerivAt ℝ c x := hc.isSymmSndFDerivAt (by simp)
  rw [mixedPartialCoord_def, mixedPartialCoord_def,
    fderiv_fderiv_apply hfd w v, fderiv_fderiv_apply hfd v w, hsymm v w,
    Geodesic.chartChristoffelContraction_symm (I := I) g α]

/-! ## Property (2): the product rule against the chart metric -/

/-- **Math.** Petersen §5.1, **property (2)** for the coordinate mixed partial: the
**product rule** in directional form. For a `C²` map `c` with `c x` in the chart
target, along the line `s ↦ x + s·z`,
$$\frac{d}{ds}\Big|_{s=0} \big\langle \partial_v c, \partial_w c \big\rangle_{c}
  = \big\langle \tfrac{\partial^2 c}{\partial z \partial v}, \partial_w c \big\rangle
  + \big\langle \partial_v c, \tfrac{\partial^2 c}{\partial z \partial w} \big\rangle,$$
all read in the chart metric at `α`. Obtained from the metric-compatibility engine
`hasDerivAt_chartMetricInner_along` applied to the curve `u(s) = c(x + s·z)` and the
vector fields `V(s) = Dc(x+s·z)·v`, `W(s) = Dc(x+s·z)·w`, whose covariant
derivatives at `s = 0` are exactly the coordinate mixed partials. -/
theorem mixedPartialCoord_productRule (g : RiemannianMetric I M) (α : M) [I.Boundaryless]
    {c : F → E} {x : F} (hc : ContDiffAt ℝ 2 c x) (hmem : c x ∈ (extChartAt I α).target)
    (v w z : F) :
    HasDerivAt (fun s : ℝ => chartMetricInner (I := I) g α (c (x + s • z))
        (fderiv ℝ c (x + s • z) v) (fderiv ℝ c (x + s • z) w))
      (chartMetricInner (I := I) g α (c x)
          (mixedPartialCoord (I := I) g α c x z v) (fderiv ℝ c x w)
        + chartMetricInner (I := I) g α (c x)
          (fderiv ℝ c x v) (mixedPartialCoord (I := I) g α c x z w)) 0 := by
  classical
  have hcdiff : DifferentiableAt ℝ c x := hc.differentiableAt (by norm_num)
  have hfd : DifferentiableAt ℝ (fderiv ℝ c) x :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgv : DifferentiableAt ℝ (fun y => fderiv ℝ c y v) x :=
    hfd.clm_apply (differentiableAt_const v)
  have hgw : DifferentiableAt ℝ (fun y => fderiv ℝ c y w) x :=
    hfd.clm_apply (differentiableAt_const w)
  -- the line `s ↦ x + s • z` and the three curves along it
  have hline : HasDerivAt (fun s : ℝ => x + s • z) z 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add x
  have hu : HasDerivAt (fun s : ℝ => c (x + s • z)) (fderiv ℝ c x z) 0 := by
    have hcx : HasFDerivAt c (fderiv ℝ c x) ((fun s : ℝ => x + s • z) 0) := by
      simpa only [zero_smul, add_zero] using hcdiff.hasFDerivAt
    exact hcx.comp_hasDerivAt 0 hline
  have hV : HasDerivAt (fun s : ℝ => fderiv ℝ c (x + s • z) v)
      (fderiv ℝ (fun y => fderiv ℝ c y v) x z) 0 := by
    have h1 : HasFDerivAt (fun y => fderiv ℝ c y v)
        (fderiv ℝ (fun y => fderiv ℝ c y v) x) ((fun s : ℝ => x + s • z) 0) := by
      simpa only [zero_smul, add_zero] using hgv.hasFDerivAt
    exact h1.comp_hasDerivAt 0 hline
  have hW : HasDerivAt (fun s : ℝ => fderiv ℝ c (x + s • z) w)
      (fderiv ℝ (fun y => fderiv ℝ c y w) x z) 0 := by
    have h1 : HasFDerivAt (fun y => fderiv ℝ c y w)
        (fderiv ℝ (fun y => fderiv ℝ c y w) x) ((fun s : ℝ => x + s • z) 0) := by
      simpa only [zero_smul, add_zero] using hgw.hasFDerivAt
    exact h1.comp_hasDerivAt 0 hline
  -- side conditions at the base point, from chart-target membership
  have hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (c x) := fun i j =>
    ((chartGramOnE_contDiffOn (I := I) g α i j).contDiffAt
      (extChartAt_target_mem_nhds' (I := I) hmem)).differentiableAt (by norm_num)
  have hbase : (extChartAt I α).symm (c x)
      ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source,
      ← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I α).map_target hmem
  -- the metric-compatibility engine, then identify the covariant derivatives
  have key := hasDerivAt_chartMetricInner_along (I := I) g α
    (fun s : ℝ => c (x + s • z)) (fun s : ℝ => fderiv ℝ c (x + s • z) v)
    (fun s : ℝ => fderiv ℝ c (x + s • z) w) (t := 0)
    hu.differentiableAt hV.differentiableAt hW.differentiableAt
    (fun i j => by simpa using hG i j) (by simpa using hbase)
  refine key.congr_deriv ?_
  simp only [covariantDerivCoord_def, mixedPartialCoord_def, hu.deriv, hV.deriv, hW.deriv,
    zero_smul, add_zero]

/-! ## The Koszul-type formula -/

/-- **Math.** The derivative at `s = 0` of the chart metric pairing of the first
partials `∂_a c, ∂_b c` along the line through `x` in the direction `v`:
`D_v ⟨∂_a c, ∂_b c⟩`. This is the first-partial data entering the right-hand side
of the Koszul formula of Petersen's Lemma 5.1.1. -/
def gramLineDeriv (g : RiemannianMetric I M) (α : M) (c : F → E) (x : F) (v a b : F) : ℝ :=
  deriv (fun s : ℝ => chartMetricInner (I := I) g α (c (x + s • v))
    (fderiv ℝ c (x + s • v) a) (fderiv ℝ c (x + s • v) b)) 0

theorem gramLineDeriv_def (g : RiemannianMetric I M) (α : M) (c : F → E) (x : F)
    (v a b : F) :
    gramLineDeriv (I := I) g α c x v a b
      = deriv (fun s : ℝ => chartMetricInner (I := I) g α (c (x + s • v))
          (fderiv ℝ c (x + s • v) a) (fderiv ℝ c (x + s • v) b)) 0 := rfl

/-- **Math.** Petersen §5.1, the **Koszul-type formula forced by the two axioms**
(the computation inside the proof of Lemma 5.1.1), abstractly. If a candidate
mixed partial `P` at the map `c` and point `x` is (1) symmetric and (2) satisfies
the product rule against the chart metric along lines, then
$$2\,\langle P(v,w), \partial_z c\rangle
  = D_v\langle \partial_w c, \partial_z c\rangle
  + D_w\langle \partial_z c, \partial_v c\rangle
  - D_z\langle \partial_v c, \partial_w c\rangle,$$
Petersen's six-term cancellation. The right-hand side involves first partials
only, so it pins `P` down against every direction `∂_z c`. -/
theorem koszul_of_symm_of_productRule (g : RiemannianMetric I M) (α : M)
    (c : F → E) (x : F) (P : F → F → E)
    (hPsymm : ∀ v w, P v w = P w v)
    (hPprod : ∀ v w z : F, HasDerivAt
      (fun s : ℝ => chartMetricInner (I := I) g α (c (x + s • z))
        (fderiv ℝ c (x + s • z) v) (fderiv ℝ c (x + s • z) w))
      (chartMetricInner (I := I) g α (c x) (P z v) (fderiv ℝ c x w)
        + chartMetricInner (I := I) g α (c x) (fderiv ℝ c x v) (P z w)) 0)
    (v w z : F) :
    2 * chartMetricInner (I := I) g α (c x) (P v w) (fderiv ℝ c x z)
      = gramLineDeriv (I := I) g α c x v w z + gramLineDeriv (I := I) g α c x w z v
        - gramLineDeriv (I := I) g α c x z v w := by
  have h1 : gramLineDeriv (I := I) g α c x v w z
      = chartMetricInner (I := I) g α (c x) (P v w) (fderiv ℝ c x z)
        + chartMetricInner (I := I) g α (c x) (fderiv ℝ c x w) (P v z) :=
    (hPprod w z v).deriv
  have h2 : gramLineDeriv (I := I) g α c x w z v
      = chartMetricInner (I := I) g α (c x) (P w z) (fderiv ℝ c x v)
        + chartMetricInner (I := I) g α (c x) (fderiv ℝ c x z) (P w v) :=
    (hPprod z v w).deriv
  have h3 : gramLineDeriv (I := I) g α c x z v w
      = chartMetricInner (I := I) g α (c x) (P z v) (fderiv ℝ c x w)
        + chartMetricInner (I := I) g α (c x) (fderiv ℝ c x v) (P z w) :=
    (hPprod v w z).deriv
  rw [h1, h2, h3, hPsymm v z, hPsymm w z, hPsymm w v,
    chartMetricInner_symm (I := I) g α (c x) (fderiv ℝ c x w) (P z v),
    chartMetricInner_symm (I := I) g α (c x) (fderiv ℝ c x z) (P v w),
    chartMetricInner_symm (I := I) g α (c x) (P z w) (fderiv ℝ c x v)]
  ring

/-- **Math.** Petersen §5.1, the **Koszul-type formula** for the coordinate mixed
partial (the computation of Lemma 5.1.1 realized by Theorem 5.1.2's operator):
`2⟨∂²c/∂v∂w, ∂_z c⟩ = D_v⟨∂_w c, ∂_z c⟩ + D_w⟨∂_z c, ∂_v c⟩ − D_z⟨∂_v c, ∂_w c⟩`,
read in the chart metric at `α`. Instantiates the abstract cancellation
`koszul_of_symm_of_productRule` with properties (1) and (2) of
`mixedPartialCoord`. -/
theorem mixedPartialCoord_koszul (g : RiemannianMetric I M) (α : M) [I.Boundaryless]
    {c : F → E} {x : F} (hc : ContDiffAt ℝ 2 c x) (hmem : c x ∈ (extChartAt I α).target)
    (v w z : F) :
    2 * chartMetricInner (I := I) g α (c x)
        (mixedPartialCoord (I := I) g α c x v w) (fderiv ℝ c x z)
      = gramLineDeriv (I := I) g α c x v w z + gramLineDeriv (I := I) g α c x w z v
        - gramLineDeriv (I := I) g α c x z v w :=
  koszul_of_symm_of_productRule (I := I) g α c x (mixedPartialCoord (I := I) g α c x)
    (fun v' w' => mixedPartialCoord_symm (I := I) g α hc v' w')
    (fun v' w' z' => mixedPartialCoord_productRule (I := I) g α hc hmem v' w' z') v w z

/-! ## Petersen's extension trick: the map `(t, y) ↦ c y + t • ξ` -/

/-- **Math.** Petersen's extension `c̃(t, y) = c(y) + t·ξ` of a map `c : F → E` by
an arbitrary vector `ξ : E` in the time direction: its total derivative at `(t, y)`
is `(s, u) ↦ Dc(y)·u + s·ξ`. -/
theorem hasFDerivAt_prodExtension {c : F → E} {y : F} (hc : DifferentiableAt ℝ c y)
    (ξ : E) (t : ℝ) :
    HasFDerivAt (fun p : ℝ × F => c p.2 + p.1 • ξ)
      ((fderiv ℝ c y).comp (ContinuousLinearMap.snd ℝ ℝ F)
        + (ContinuousLinearMap.fst ℝ ℝ F).smulRight ξ) (t, y) := by
  have h1 : HasFDerivAt (fun p : ℝ × F => c p.2)
      ((fderiv ℝ c y).comp (ContinuousLinearMap.snd ℝ ℝ F)) (t, y) :=
    hc.hasFDerivAt.comp (t, y) hasFDerivAt_snd
  have h2 : HasFDerivAt (fun p : ℝ × F => p.1 • ξ)
      ((ContinuousLinearMap.fst ℝ ℝ F).smulRight ξ) (t, y) :=
    ((ContinuousLinearMap.fst ℝ ℝ F).smulRight ξ).hasFDerivAt
  exact h1.add h2

/-- **Math.** The derivative of Petersen's extension `c̃(t, y) = c(y) + t·ξ` in the
direction `(s, u)`: `Dc̃(t, y)·(s, u) = Dc(y)·u + s·ξ`. In particular the slice
directions `(0, u)` recover the first partials of `c` and the time direction
`(1, 0)` produces the arbitrary test vector `ξ`. -/
theorem fderiv_prodExtension_apply {c : F → E} {y : F} (hc : DifferentiableAt ℝ c y)
    (ξ : E) (t s : ℝ) (u : F) :
    fderiv ℝ (fun p : ℝ × F => c p.2 + p.1 • ξ) (t, y) (s, u)
      = fderiv ℝ c y u + s • ξ := by
  rw [(hasFDerivAt_prodExtension hc ξ t).fderiv]
  simp

/-- **Math.** Petersen's extension `c̃(t, y) = c(y) + t·ξ` of a `C²` map is `C²`. -/
theorem contDiffAt_prodExtension {c : F → E} {x : F} (hc : ContDiffAt ℝ 2 c x) (ξ : E) :
    ContDiffAt ℝ 2 (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x) := by
  have h1 : ContDiffAt ℝ 2 (fun p : ℝ × F => c p.2) ((0 : ℝ), x) :=
    hc.comp ((0 : ℝ), x) contDiff_snd.contDiffAt
  have h2 : ContDiffAt ℝ 2 (fun p : ℝ × F => p.1 • ξ) ((0 : ℝ), x) :=
    (contDiff_fst.smul contDiff_const).contDiffAt
  exact h1.add h2

/-- **Math.** **Slice-naturality of the coordinate mixed partial** for Petersen's
extension: the mixed partial of `c̃(t, y) = c(y) + t·ξ` at `(0, x)` in the slice
directions `(0, v)`, `(0, w)` is the mixed partial of `c` at `x` in the directions
`v, w` — the extension is affine in `t`, so it contributes nothing to slice
derivatives. This identifies the `mixedPartialCoord` side of the uniqueness
argument after the extension trick. -/
theorem mixedPartialCoord_prodExtension_slice (g : RiemannianMetric I M) (α : M)
    {c : F → E} {x : F} (hc : ContDiffAt ℝ 2 c x) (ξ : E) (v w : F) :
    mixedPartialCoord (I := I) g α (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x)
        ((0 : ℝ), v) ((0 : ℝ), w)
      = mixedPartialCoord (I := I) g α c x v w := by
  have hcdiff : DifferentiableAt ℝ c x := hc.differentiableAt (by norm_num)
  have hfd : DifferentiableAt ℝ (fderiv ℝ c) x :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgw : DifferentiableAt ℝ (fun y => fderiv ℝ c y w) x :=
    hfd.clm_apply (differentiableAt_const w)
  -- first-derivative slices
  have hfd_v : fderiv ℝ (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x) ((0 : ℝ), v)
      = fderiv ℝ c x v := by
    simpa using fderiv_prodExtension_apply hcdiff ξ 0 0 v
  have hfd_w : fderiv ℝ (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x) ((0 : ℝ), w)
      = fderiv ℝ c x w := by
    simpa using fderiv_prodExtension_apply hcdiff ξ 0 0 w
  -- the `w`-slice of the extension derivative agrees with `p ↦ Dc(p₂)·w` near `(0, x)`
  have hev : (fun p : ℝ × F => fderiv ℝ (fun q : ℝ × F => c q.2 + q.1 • ξ) p ((0 : ℝ), w))
      =ᶠ[𝓝 ((0 : ℝ), x)] fun p : ℝ × F => fderiv ℝ c p.2 w := by
    have hnear : ∀ᶠ p : ℝ × F in 𝓝 ((0 : ℝ), x), DifferentiableAt ℝ c p.2 := by
      have h1 : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 c y := hc.eventually (by simp)
      exact continuousAt_snd.tendsto.eventually
        (h1.mono fun y hy => hy.differentiableAt (by norm_num))
    filter_upwards [hnear] with p hp
    simpa using fderiv_prodExtension_apply hp ξ p.1 0 w
  -- second-derivative slice, by differentiating through the second projection
  have hkey : fderiv ℝ
      (fun p : ℝ × F => fderiv ℝ (fun q : ℝ × F => c q.2 + q.1 • ξ) p ((0 : ℝ), w))
      ((0 : ℝ), x) ((0 : ℝ), v) = fderiv ℝ (fun y => fderiv ℝ c y w) x v := by
    rw [hev.fderiv_eq]
    have hsnd : HasFDerivAt (Prod.snd : ℝ × F → F) (ContinuousLinearMap.snd ℝ ℝ F)
        ((0 : ℝ), x) := hasFDerivAt_snd
    have hcomp := hgw.hasFDerivAt.comp ((0 : ℝ), x) hsnd
    have hcomp2 : HasFDerivAt (fun p : ℝ × F => fderiv ℝ c p.2 w)
        ((fderiv ℝ (fun y => fderiv ℝ c y w) x).comp (ContinuousLinearMap.snd ℝ ℝ F))
        ((0 : ℝ), x) := hcomp
    rw [hcomp2.fderiv]
    simp
  have hpt : c (((0 : ℝ), x) : ℝ × F).2 + (((0 : ℝ), x) : ℝ × F).1 • ξ = c x := by simp
  rw [mixedPartialCoord_def, mixedPartialCoord_def, hkey, hfd_v, hfd_w, hpt]

/-! ## Lemma 5.1.1 and Theorem 5.1.2 -/

/-- **Math.** **Petersen, Lemma 5.1.1 (uniqueness of mixed partials).** Let `D` be
any operator assigning to (two-variable extensions of) maps into the chart target
a candidate mixed second partial, satisfying Petersen's two axioms:
* (1) `hsymm` — symmetry in the two directions at every `C²` point;
* (2) `hprod` — the product rule against the chart metric along lines, at every
  `C²` point mapped into the chart target;
and compatible with time-slicing (`hslice`, relating `D` on maps `ℝ × F → E` to a
slice operator `D₀` on maps `F → E`). Then `D₀` is **forced** to agree with the
chart-coordinate mixed partial `mixedPartialCoord`.

The proof is Petersen's extension trick: for arbitrary `ξ : E`, extend `c` to
`c̃(t, y) = c(y) + t·ξ`, so that `Dc̃(0, x)·(1, 0) = ξ` while all slice data of `c̃`
is that of `c`. The Koszul formula forced by (1)+(2)
(`koszul_of_symm_of_productRule`) applied to both `D` and `mixedPartialCoord` at
`c̃` in the directions `(0, v)`, `(0, w)`, `(1, 0)` has the *same* right-hand side
(first-partial data of `c̃` only), whence
`⟨D₀ c x v w, ξ⟩ = ⟨mixedPartialCoord g α c x v w, ξ⟩` for every `ξ`; the chart
metric being nondegenerate at chart points (`chartMetricInner_nondegenerate`), the
two mixed partials coincide. -/
theorem mixedPartials_uniqueness (g : RiemannianMetric I M) (α : M) [I.Boundaryless]
    (D₀ : (F → E) → F → F → F → E)
    (D : ((ℝ × F) → E) → (ℝ × F) → (ℝ × F) → (ℝ × F) → E)
    (hslice : ∀ (ct : (ℝ × F) → E) (x : F) (v w : F), ContDiffAt ℝ 2 ct (0, x) →
      D ct (0, x) (0, v) (0, w) = D₀ (fun y => ct (0, y)) x v w)
    (hsymm : ∀ (ct : (ℝ × F) → E) (x v w : ℝ × F), ContDiffAt ℝ 2 ct x →
      D ct x v w = D ct x w v)
    (hprod : ∀ (ct : (ℝ × F) → E) (x : ℝ × F) (v w z : ℝ × F), ContDiffAt ℝ 2 ct x →
      ct x ∈ (extChartAt I α).target →
      HasDerivAt (fun s : ℝ => chartMetricInner (I := I) g α (ct (x + s • z))
          (fderiv ℝ ct (x + s • z) v) (fderiv ℝ ct (x + s • z) w))
        (chartMetricInner (I := I) g α (ct x) (D ct x z v) (fderiv ℝ ct x w)
          + chartMetricInner (I := I) g α (ct x) (fderiv ℝ ct x v) (D ct x z w)) 0)
    (c : F → E) (x : F) (v w : F) (hc : ContDiffAt ℝ 2 c x)
    (hmem : c x ∈ (extChartAt I α).target) :
    D₀ c x v w = mixedPartialCoord (I := I) g α c x v w := by
  classical
  -- pair both candidates against an arbitrary `ξ` via the extension trick
  have key : ∀ ξ : E,
      chartMetricInner (I := I) g α (c x) (D₀ c x v w) ξ
        = chartMetricInner (I := I) g α (c x) (mixedPartialCoord (I := I) g α c x v w) ξ := by
    intro ξ
    have hct2 : ContDiffAt ℝ 2 (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x) :=
      contDiffAt_prodExtension hc ξ
    have hctmem : (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x)
        ∈ (extChartAt I α).target := by simpa using hmem
    -- the abstract Koszul formula, for `D` and for `mixedPartialCoord`, at the extension
    have hK_D := koszul_of_symm_of_productRule (I := I) g α
      (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x)
      (D (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x))
      (fun v' w' => hsymm (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x) v' w' hct2)
      (fun v' w' z' => hprod (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x) v' w' z'
        hct2 hctmem)
      ((0 : ℝ), v) ((0 : ℝ), w) ((1 : ℝ), (0 : F))
    have hK_mp := koszul_of_symm_of_productRule (I := I) g α
      (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x)
      (mixedPartialCoord (I := I) g α (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x))
      (fun v' w' => mixedPartialCoord_symm (I := I) g α hct2 v' w')
      (fun v' w' z' => mixedPartialCoord_productRule (I := I) g α hct2 hctmem v' w' z')
      ((0 : ℝ), v) ((0 : ℝ), w) ((1 : ℝ), (0 : F))
    -- normalize the base point `c̃(0, x)` to `c x`
    simp only [zero_smul, add_zero] at hK_D hK_mp
    -- identify the slice data
    have hDslice : D (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x)
        ((0 : ℝ), v) ((0 : ℝ), w) = D₀ c x v w := by
      simpa using hslice (fun p : ℝ × F => c p.2 + p.1 • ξ) x v w hct2
    have hxi : fderiv ℝ (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x)
        ((1 : ℝ), (0 : F)) = ξ := by
      simpa using fderiv_prodExtension_apply (hc.differentiableAt (by norm_num)) ξ 0 1 0
    rw [hDslice, hxi] at hK_D
    rw [mixedPartialCoord_prodExtension_slice (I := I) g α hc ξ v w, hxi] at hK_mp
    linarith [hK_D, hK_mp]
  -- nondegeneracy of the chart metric finishes
  have hsub : D₀ c x v w - mixedPartialCoord (I := I) g α c x v w = 0 :=
    chartMetricInner_nondegenerate (I := I) g α hmem
      (fun ξ => by rw [chartMetricInner_sub_left, key ξ, sub_self])
  exact sub_eq_zero.mp hsub

/-- **Math.** **Petersen, Theorem 5.1.2 (existence of mixed partials).** The
chart-coordinate mixed partial `mixedPartialCoord` — Petersen's Γ-corrected
coordinate formula — satisfies the two characterizing properties:
**(1)** symmetry `∂²c/∂v∂w = ∂²c/∂w∂v` at every `C²` point, and **(2)** the
product rule against the chart metric along lines, at every `C²` point mapped
into the chart target. Together with Lemma 5.1.1 (`mixedPartials_uniqueness`)
this characterizes `mixedPartialCoord` completely. -/
theorem mixedPartials_existence (g : RiemannianMetric I M) (α : M) [I.Boundaryless] :
    (∀ (c : F → E) (x : F) (v w : F), ContDiffAt ℝ 2 c x →
        mixedPartialCoord (I := I) g α c x v w = mixedPartialCoord (I := I) g α c x w v)
      ∧ (∀ (c : F → E) (x : F) (v w z : F), ContDiffAt ℝ 2 c x →
          c x ∈ (extChartAt I α).target →
          HasDerivAt (fun s : ℝ => chartMetricInner (I := I) g α (c (x + s • z))
              (fderiv ℝ c (x + s • z) v) (fderiv ℝ c (x + s • z) w))
            (chartMetricInner (I := I) g α (c x)
                (mixedPartialCoord (I := I) g α c x z v) (fderiv ℝ c x w)
              + chartMetricInner (I := I) g α (c x)
                (fderiv ℝ c x v) (mixedPartialCoord (I := I) g α c x z w)) 0) :=
  ⟨fun _c _x v w hc => mixedPartialCoord_symm (I := I) g α hc v w,
   fun _c _x v w z hc hmem => mixedPartialCoord_productRule (I := I) g α hc hmem v w z⟩

end PetersenLib

end
