import PetersenLib.Ch03.CurvatureCoordinates
import PetersenLib.Riemannian.Jacobi.SurfaceCurvatureCommutation
import PetersenLib.Riemannian.Jacobi.ChartCurvatureNaturality

/-!
# Petersen Ch. 6, §6.1 — the coordinate curvature ↔ abstract curvature bridge

Petersen's Lemma 6.1.2 (`lem:pet-ch6-third-partial-commutator`) equates a *third-partial
commutator* of a map into `M` with the **curvature tensor** `R` of Ch. 3.  The commutator
half of that identity is a coordinate computation, and it is already available as
`PetersenLib.Jacobi.surface_covariant_commutator`
(`Riemannian/Jacobi/SurfaceCurvatureCommutation.lean`, do Carmo Ch. 4 Lemma 4.1) —
but it produces the *coordinate* curvature `chartCurvatureContraction2`, an expression in
the chart Christoffel symbols, not Ch. 3's Koszul-defined `curvatureTensorAt`.

This file closes that last gap:

* `Tensor.chartBasisVecFiber_self` — **at the centre of its own chart the chart frame is
  the model basis**, `∂_i|_p = e_i`.  The trivialization at `p` restricted to the fibre
  over `p` is the identity (`tangentCoordChange_self`).
* `sum_chartCoord_smul_chartBasisVecFiber_self` — consequently the chart-frame expansion
  of a tangent vector at `p` is just `Basis.sum_repr`: `∑_a v^a ∂_a|_p = v`.
* `curvatureTensorAt_sum_first/_middle/_field`, `curvatureTensorAt_sum₃` — `R` is
  trilinear over finite sums, by induction from Ch. 3's six add/smul clauses.
* `chartCurvatureContraction2_eq_neg_curvatureTensorAt` — **the bridge**:
  `R_chart(X, Y)Z = − R(X, Y)Z` at the centre of the chart at `p`.
* `chartCurvature_eq_curvatureTensorAt` — **the same bridge in vector form**, for the other
  vendored presentation of the chart curvature: `ℛ_chart(A, B)C = R(A, B)C`, sign-free,
  because the do Carmo↔Petersen sign flip cancels against the slot swap between the two
  the alternative presentations (`Riemannian/Jacobi/ChartCurvatureNaturality.lean`).  Serves no
  blueprint node of its own; banked infrastructure.  It is diagonal-only, and its docstring
  records why that is fatal for Jacobi existence/uniqueness.

## The sign

do Carmo's convention is `R(X,Y) = ∇_Y∇_X − ∇_X∇_Y + ∇_{[X,Y]}`; Petersen's (Ch. 3's
`curvatureTensor`) is `R(X,Y) = ∇_X∇_Y − ∇_Y∇_X − ∇_{[X,Y]}`.  The two coefficient
expressions are *exact negations* with the same index slots:

* Petersen (`curvatureTensor_coordinates`):
  `R^l_{ijk} = ∂_iΓ^l_{jk} − ∂_jΓ^l_{ik} + Σ_s(Γ^s_{jk}Γ^l_{is} − Γ^s_{ik}Γ^l_{js})`;
* do Carmo (`chartCurvatureCoef`):
  `R^l_{ijk} = ∂_jΓ^l_{ik} − ∂_iΓ^l_{jk} + Σ_s(Γ^s_{ik}Γ^l_{js} − Γ^s_{jk}Γ^l_{is})`.

Hence the minus sign in the bridge.  Downstream, in Lemma 6.1.2, it cancels against the
direction swap between the two conventions' commutators — which is why Petersen's
`R(∂_uc, ∂_sc)∂_tc` and do Carmo's `R(∂f/∂s, ∂f/∂t)V` agree.

## Why the diagonal suffices

`curvatureTensor_coordinates` is stated *on the diagonal*: the chart is centred at `p` and
the coefficient is evaluated at `extChartAt I p p`.  That is exactly the generality Lemma
6.1.2 needs, since its conclusion is pointwise at `p = c(u₀,s₀,t₀)`: specialising the
fixed chart to `α := p` puts the evaluation point at the chart centre.
-/

open Set Filter Bundle Manifold
open scoped Manifold Topology ContDiff Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The chart frame at the centre of its own chart -/

namespace Tensor

/-- **Math.** **At the centre of its own chart the chart frame is the model basis**:
`∂_i|_p = e_i` under the defeq `TangentSpace I p = E`.  The chart frame at `α` is defined
by pulling the model basis back through the trivialization at `α`, and at the base point
`α = p` that trivialization is the identity on the fibre — this is
`tangentCoordChange_self`, the tangent coordinate change from a chart to itself.

This is what makes the *diagonal* coordinate formula `curvatureTensor_coordinates` usable:
the chart-frame expansion at `p` collapses to the plain basis expansion of `E`. -/
theorem chartBasisVecFiber_self (p : M) (i : Fin (Module.finrank ℝ E)) :
    (chartBasisVecFiber (I := I) p i p : E) = (Module.finBasis ℝ E) i := by
  rw [chartBasisVecFiber,
    show (trivializationAt E (TangentSpace I) p).symm p
        = (trivializationAt E (TangentSpace I) p).symmL ℝ p from rfl,
    TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source H p)]
  exact tangentCoordChange_self (I := I) (x := p) (z := p) (mem_extChartAt_source (I := I) p)

end Tensor

/-- **Math.** The **chart-frame expansion of a tangent vector at the chart centre** is the
basis expansion of `E`: `∑_a v^a ∂_a|_p = v`, with `v^a = chartCoord a v` the coordinates
in the model basis.  Immediate from `Tensor.chartBasisVecFiber_self` and `Basis.sum_repr`. -/
theorem sum_chartCoord_smul_chartBasisVecFiber_self (p : M) (v : TangentSpace I p) :
    ∑ a, Geodesic.chartCoord (E := E) a v • (chartBasisVecFiber (I := I) p a p : E) = v := by
  simp only [Tensor.chartBasisVecFiber_self, Geodesic.chartCoord_def]
  exact (Module.finBasis ℝ E).sum_repr v

/-! ### Trilinearity of the pointwise curvature tensor over finite sums

From here on the full `Ch03/CurvaturePointwise.lean` instance bundle is in force: the
pointwise tensor is defined by bump-extending tangent vectors to global smooth fields,
which needs `[SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M] [I.Boundaryless]`. -/

variable [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Math.** `R(·, v)w` kills the zero vector — the `c = 0` case of
`curvatureTensorAt_smul_first`. -/
theorem curvatureTensorAt_zero_first (D : AffineConnection I M) (p : M)
    (v w : TangentSpace I p) : curvatureTensorAt D p 0 v w = 0 := by
  have h := curvatureTensorAt_smul_first D p (0 : ℝ) 0 v w
  rwa [zero_smul, zero_smul] at h

/-- **Math.** `R(u, ·)w` kills the zero vector. -/
theorem curvatureTensorAt_zero_middle (D : AffineConnection I M) (p : M)
    (u w : TangentSpace I p) : curvatureTensorAt D p u 0 w = 0 := by
  have h := curvatureTensorAt_smul_middle D p (0 : ℝ) u 0 w
  rwa [zero_smul, zero_smul] at h

/-- **Math.** `R(u, v)·` kills the zero vector. -/
theorem curvatureTensorAt_zero_field (D : AffineConnection I M) (p : M)
    (u v : TangentSpace I p) : curvatureTensorAt D p u v 0 = 0 := by
  have h := curvatureTensorAt_smul_field D p (0 : ℝ) u v 0
  rwa [zero_smul, zero_smul] at h

/-- **Math.** Additivity of `R` in its **first** slot over a finite sum. -/
theorem curvatureTensorAt_sum_first (D : AffineConnection I M) (p : M)
    (s : Finset ι) (f : ι → TangentSpace I p) (v w : TangentSpace I p) :
    curvatureTensorAt D p (∑ i ∈ s, f i) v w
      = ∑ i ∈ s, curvatureTensorAt D p (f i) v w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using curvatureTensorAt_zero_first D p v w
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, curvatureTensorAt_add_first, ih]

/-- **Math.** Additivity of `R` in its **middle** slot over a finite sum. -/
theorem curvatureTensorAt_sum_middle (D : AffineConnection I M) (p : M)
    (s : Finset ι) (f : ι → TangentSpace I p) (u w : TangentSpace I p) :
    curvatureTensorAt D p u (∑ j ∈ s, f j) w
      = ∑ j ∈ s, curvatureTensorAt D p u (f j) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using curvatureTensorAt_zero_middle D p u w
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, curvatureTensorAt_add_middle, ih]

/-- **Math.** Additivity of `R` in its **field** slot over a finite sum. -/
theorem curvatureTensorAt_sum_field (D : AffineConnection I M) (p : M)
    (s : Finset ι) (f : ι → TangentSpace I p) (u v : TangentSpace I p) :
    curvatureTensorAt D p u v (∑ k ∈ s, f k)
      = ∑ k ∈ s, curvatureTensorAt D p u v (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using curvatureTensorAt_zero_field D p u v
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, curvatureTensorAt_add_field, ih]

/-- **Math.** **`R` is trilinear**: expanding all three arguments over a finite family,
`R(∑_i a_i e_i, ∑_j b_j e_j, ∑_k c_k e_k) = ∑_{i,j,k} a_i b_j c_k · R(e_i, e_j, e_k)`.
This is the form the chart bridge needs — it turns the general-vector statement into the
basis statement `curvatureTensor_coordinates` proves. -/
theorem curvatureTensorAt_sum₃ (D : AffineConnection I M) (p : M)
    (a b c : ι → ℝ) (e : ι → TangentSpace I p) :
    curvatureTensorAt D p (∑ i, a i • e i) (∑ j, b j • e j) (∑ k, c k • e k)
      = ∑ i, ∑ j, ∑ k, (a i * b j * c k) • curvatureTensorAt D p (e i) (e j) (e k) := by
  classical
  rw [curvatureTensorAt_sum_first]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [curvatureTensorAt_smul_first, curvatureTensorAt_sum_middle, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [curvatureTensorAt_smul_middle, curvatureTensorAt_sum_field, Finset.smul_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [curvatureTensorAt_smul_field, smul_smul, smul_smul]

/-! ### The bridge -/

/-- **Math.** **The bridge on the chart frame.** Ch. 3's abstract curvature tensor applied
to a chart-frame triple at the chart centre is the *negative* of do Carmo's coordinate
curvature coefficient:
`R(∂_i, ∂_j)∂_k = ∑_l (− Rˡ_{ijk}) e_l`.

This is `curvatureTensor_coordinates` (Petersen's `R^l_{ijk} = ∂_iΓ^l_{jk} − ∂_jΓ^l_{ik}
+ Γ^s_{jk}Γ^l_{is} − Γ^s_{ik}Γ^l_{js}`) with `christoffelSymbols_metric_formula` turning
the abstract `christoffelSymbolsSecondKind` of its quadratic term into the *chart*
`chartChristoffel` that `chartCurvatureCoef` is written in, after which the two
coefficient expressions are related by `ring` — they are exact negations. -/
theorem curvatureTensorAt_chartBasis_eq_neg_chartCurvatureCoef (g : RiemannianMetric I M)
    (p : M) (i j k : Fin (Module.finrank ℝ E)) :
    curvatureTensorAt (g.leviCivita).toAffineConnection p
        (chartBasisVecFiber (I := I) p i p) (chartBasisVecFiber (I := I) p j p)
        (chartBasisVecFiber (I := I) p k p)
      = ∑ l, (-(Jacobi.chartCurvatureCoef (I := I) g p i j k l (extChartAt I p p)))
          • ((Module.finBasis ℝ E) l : E) := by
  classical
  rw [curvatureTensor_coordinates (I := I) g p i j k]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Tensor.chartBasisVecFiber_self]
  congr 1
  simp only [Jacobi.chartCurvatureCoef, christoffelSymbols_metric_formula]
  -- the two quadratic terms are termwise negations of one another
  have hS : ∀ s, chartChristoffel (I := I) g p i k s (extChartAt I p p)
        * chartChristoffel (I := I) g p j s l (extChartAt I p p)
      - chartChristoffel (I := I) g p j k s (extChartAt I p p)
        * chartChristoffel (I := I) g p i s l (extChartAt I p p)
      = -(chartChristoffel (I := I) g p j k s (extChartAt I p p)
            * chartChristoffel (I := I) g p i s l (extChartAt I p p)
          - chartChristoffel (I := I) g p i k s (extChartAt I p p)
            * chartChristoffel (I := I) g p j s l (extChartAt I p p)) := fun s => by ring
  simp only [hS, Finset.sum_neg_distrib]
  ring

/-- **Math.** **The bridge**, Petersen §6.1 / do Carmo Ch. 4: at the centre of the chart at
`p`, the coordinate curvature contraction of
`Riemannian/Jacobi/SurfaceCurvatureCommutation.lean` is the *negative* of Ch. 3's
abstract curvature tensor:
`R_chart(X, Y)Z = − R(X, Y)Z`.

Expand `X, Y, Z` over the chart frame at `p` — which by
`sum_chartCoord_smul_chartBasisVecFiber_self` is just the model basis of `E` — apply
trilinearity (`curvatureTensorAt_sum₃`), and compare coefficients with
`curvatureTensorAt_chartBasis_eq_neg_chartCurvatureCoef`.

This is the identity that lets Petersen's Lemma 6.1.2 be read off the vendored
`surface_covariant_commutator`, which produces its right-hand side in coordinates. -/
theorem chartCurvatureContraction2_eq_neg_curvatureTensorAt (g : RiemannianMetric I M)
    (p : M) (X Y Z : TangentSpace I p) :
    Jacobi.chartCurvatureContraction2 (I := I) g p X Y Z (extChartAt I p p)
      = -curvatureTensorAt (g.leviCivita).toAffineConnection p X Y Z := by
  classical
  conv_rhs => rw [← sum_chartCoord_smul_chartBasisVecFiber_self (I := I) p X,
    ← sum_chartCoord_smul_chartBasisVecFiber_self (I := I) p Y,
    ← sum_chartCoord_smul_chartBasisVecFiber_self (I := I) p Z]
  rw [curvatureTensorAt_sum₃]
  simp only [curvatureTensorAt_chartBasis_eq_neg_chartCurvatureCoef,
    Jacobi.chartCurvatureContraction2, Finset.smul_sum, smul_smul, Finset.sum_smul,
    ← Finset.sum_neg_distrib, ← neg_smul]
  -- both sides are the same fourfold sum; move the basis index `l` from outermost to
  -- innermost to match
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  ring

/-! ### The bridge in vector form -/

/-- **Math.** **The bridge, vector form**, Petersen §6.1 / Morgan–Tian §1.2: at the centre of
the chart at `p`, the vendored chart curvature *vector* `chartCurvature`
(`Riemannian/Jacobi/ChartCurvatureVector.lean`, built from `christoffelCurvature` of the
bilinear Christoffel field) **is** Ch. 3's abstract `curvatureTensorAt` — with no sign:
`ℛ_chart(A, B)C = R(A, B)C`.

Two sign flips cancel, and both are traps.  `chartCurvatureContraction2_eq_neg_curvatureTensorAt`
above supplies one minus (do Carmo's convention vs. Petersen's).  The other comes from the
**slot swap** in `Jacobi.chartCurvatureContraction2_eq_chartCurvature`, which reads
`chartCurvatureContraction2 X Y Z = chartCurvature Y X Z`: the two the alternative presentations of
the *same* Morgan–Tian curvature disagree on the order of their first two slots.  So the
contraction lemma must be fed `B A C`, not `A B C`, and the resulting
`curvatureTensorAt … B A C` is turned back by `curvatureTensorAt_antisymm_first` — the
*pointwise* antisymmetry.  (`curvatureTensor_antisymm_first`, the field-level version in
`Ch03/CurvatureTensor.lean`, is the wrong lemma here and will not apply.)

**Diagonal — but no longer a blocker.  Use `chartCurvature_eq_curvatureTensorAt_of_mem`
(`Ch06/CurvatureChartBridgeMoving.lean`) instead when the foot moves.**  This statement fires
only at `y = extChartAt I p p`, the chart centre; that is a property of *this lemma*, not of
the mathematics.

An earlier version of this note claimed the restriction was essential — that
"the missing ingredient is a moving-point coordinate expansion of `curvatureTensor` that
Petersen does not have", and that Jacobi-field existence/uniqueness therefore could not be
closed.  **That was false**, and it misdirected several sessions.  Petersen had every part;
they were merely never assembled.  Diagonality entered Ch. 3 through two *cosmetic* steps —
`chartFrameField_apply_self`, and `christoffelSymbols_metric_formula` converting the abstract
`christoffelSymbolsSecondKind` into `chartChristoffel` at the centre.  Staying inside
`chartChristoffel g α · (extChartAt I α x)` throughout makes both vanish; the lever is
`exists_chartFrame_leviCivita_christoffel_nhds` (`Ch06/ChartConnectionBridge.lean`), which
supplies the Christoffel identity on a whole *open set* in an *arbitrary* chart.

`Ch06/CurvatureChartBridgeMoving.lean` carries the moving-point forms out of that
observation, and machine-checks that they subsume the diagonal ones here under
`tangentCoordChange_self`.  The Jacobi ODE's moving chart point `u t = φ_α(c t)` in one fixed
chart `α` is exactly what they handle. -/
theorem chartCurvature_eq_curvatureTensorAt [I.Boundaryless] (g : RiemannianMetric I M) (p : M)
    (A B C : TangentSpace I p) :
    Jacobi.chartCurvature (I := I) g p (extChartAt I p p) A B C
      = curvatureTensorAt (g.leviCivita).toAffineConnection p A B C := by
  have hy : (extChartAt I p p) ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p (mem_extChartAt_target (I := I) p)
  have h1 := Jacobi.chartCurvatureContraction2_eq_chartCurvature (I := I) g p B A C hy
  have h2 := chartCurvatureContraction2_eq_neg_curvatureTensorAt (I := I) g p B A C
  rw [← h1, h2, curvatureTensorAt_antisymm_first, neg_neg]

end PetersenLib

end
