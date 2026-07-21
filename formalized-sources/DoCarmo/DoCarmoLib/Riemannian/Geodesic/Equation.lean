import DoCarmoLib.Riemannian.Connection.ChartChristoffelSmooth
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Shift


/-!
# Geodesic equation in chart coordinates

For a smooth Riemannian metric `g` on a smooth manifold `M` and a curve
`γ : ℝ → M`, the geodesic equation in the chart at a point `α : M` reads
$$u''(t) + \Gamma^k{}_{ij}(g, \alpha)(u(t))\, u'^i(t)\, u'^j(t) = 0,
  \qquad u(t) := \varphi_\alpha (\gamma(t)),$$
where `Γ` is the chart-coordinate Christoffel symbol provided by
`chartChristoffel g α` (see `DifferentialGeometry/Geometry/Operator/Hessian.lean`).

This file packages:

* `chartChristoffelContraction g α v w y` — the `E`-valued contraction
  `(v^i, w^j) ↦ ∑_k (∑_{ij} Γ^k_{ij}(g, α)(y) · v^i · w^j) e_k`, where
  `e_k = Module.finBasis ℝ E k` is the fixed model-space basis used
  consistently throughout the project's chart-local pipeline.

* `geodesicVectorField g p` — the second-order vector field on the tangent
  bundle `TangentBundle I M` whose first chart component is `v` (the fibre
  coordinate of `p`) and whose second chart component is
  `-Γ(p.proj)(v, v)`, evaluated in the canonical chart at `p.proj`. The
  classical theorem (which is *not* established here) is that integral
  curves of this vector field are exactly the canonical lifts of geodesics.

* `geodesicVectorFieldChart g α p` — the second-order vector field on the
  tangent bundle written in the FIXED chart at `α : M`. This is the form
  used by chart-local Picard-Lindelöf because its smoothness on the chart
  domain is unconditional.

* `HasGeodesicEquationAt g γ t` — the explicit chart-local second-order
  geodesic equation in the canonical chart centred at the foot point
  `γ t`. This moving-foot equation is the intrinsic, chart-independent
  formulation of the geodesic condition at a single time.

* `IsGeodesic g γ`, `IsGeodesicOn g γ s` — the public geodesic predicates,
  defined intrinsically as `HasGeodesicEquationAt g γ t` at every time `t`
  (respectively at every `t ∈ s`). Because the equation is read in the
  chart at the moving foot point, these predicates remain meaningful for
  geodesics that leave any single chart.

* `IsGeodesicAt g γ t₀` — the local integral-curve predicate for the
  chart-fixed geodesic spray. A curve `γ : ℝ → M` satisfies it if there
  exists a basepoint `α : M` and a lifted curve `f : ℝ → TangentBundle I M`
  projecting to `γ`, such that `f` is a local integral curve of the
  chart-fixed geodesic vector field at `α` in a neighbourhood of `t₀`.
  This is the spray-existence interface fed by Picard-Lindelöf; the bridge
  from `IsGeodesicAt` to `HasGeodesicEquationAt` is a separate downstream
  development.

A handful of basic properties is recorded: the constant curve is a
geodesic, and reparametrisation by a time translation `t ↦ t + b`
preserves the geodesic property. The affine reparametrisation
`t ↦ a · t + b` for `a ≠ 1` and the flat-Christoffel reduction are not
recorded here; both require a manifold-derivative computation on the
tangent bundle that is best handled separately.

Smoothness, existence, and uniqueness of geodesics are not addressed in
this file; they are downstream of the chart-Christoffel smoothness already
recorded in `Integral/Connection/ChartMetric.lean` and Picard–Lindelöf.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


/-- **Math.** The `i`-th chart-basis coordinate of a vector `v : E`, taken with respect
to the canonical chart-model basis `Module.finBasis ℝ E`. -/
def chartCoord (i : Fin (Module.finrank ℝ E)) (v : E) : ℝ :=
  (Module.finBasis ℝ E).repr v i

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartCoord_def (i : Fin (Module.finrank ℝ E)) (v : E) :
    chartCoord (E := E) i v = (Module.finBasis ℝ E).repr v i := rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartCoord_smul (i : Fin (Module.finrank ℝ E)) (a : ℝ) (v : E) :
    chartCoord (E := E) i (a • v) = a * chartCoord (E := E) i v := by
  simp [chartCoord, map_smul]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartCoord_zero (i : Fin (Module.finrank ℝ E)) :
    chartCoord (E := E) i (0 : E) = 0 := by
  simp [chartCoord]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartCoord_add (i : Fin (Module.finrank ℝ E)) (v w : E) :
    chartCoord (E := E) i (v + w) = chartCoord (E := E) i v + chartCoord (E := E) i w := by
  simp [chartCoord, map_add]

/-- **Math.** The chart-coordinate Christoffel contraction. As a function of the
vector arguments `v, w : E`, this is the bilinear expression
$$\Gamma(g, \alpha)(v, w)(y) = \sum_k \Big(\sum_{i, j}
    \Gamma^k{}_{ij}(g, \alpha)(y) \cdot v^i \cdot w^j\Big) \cdot e_k.$$
-/
def chartChristoffelContraction (g : RiemannianMetric I M) (α : M)
    (v w : E) (y : E) : E :=
  ∑ k : Fin (Module.finrank ℝ E),
    (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i v * chartCoord (E := E) j w) •
      Module.finBasis ℝ E k

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartChristoffelContraction_def
    (g : RiemannianMetric I M) (α : M) (v w : E) (y : E) :
    chartChristoffelContraction (I := I) g α v w y =
      ∑ k : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α i j k y *
              chartCoord (E := E) i v * chartCoord (E := E) j w) •
          Module.finBasis ℝ E k := rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The Christoffel contraction is symmetric in its vector arguments,
inherited from the symmetry of `chartChristoffel` in its lower indices. -/
lemma chartChristoffelContraction_symm
    (g : RiemannianMetric I M) (α : M) (v w : E) (y : E) :
    chartChristoffelContraction (I := I) g α v w y =
      chartChristoffelContraction (I := I) g α w v y := by
  classical
  unfold chartChristoffelContraction
  refine Finset.sum_congr rfl ?_
  intro k _
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [chartChristoffel_symm (I := I) g α j i k y]
  ring

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Linearity of the Christoffel contraction in its first argument. -/
lemma chartChristoffelContraction_zero_left
    (g : RiemannianMetric I M) (α : M) (w : E) (y : E) :
    chartChristoffelContraction (I := I) g α (0 : E) w y = 0 := by
  classical
  unfold chartChristoffelContraction
  refine Finset.sum_eq_zero ?_
  intro k _
  have : (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i (0 : E) * chartCoord (E := E) j w) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _
    refine Finset.sum_eq_zero ?_
    intro j _
    simp
  rw [this, zero_smul]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The Christoffel contraction scales like a `(2, 0)`-tensor on its vector
slots: `Γ(a v, a v)(y) = a^2 · Γ(v, v)(y)`. -/
lemma chartChristoffelContraction_smul_smul
    (g : RiemannianMetric I M) (α : M) (a : ℝ) (v : E) (y : E) :
    chartChristoffelContraction (I := I) g α (a • v) (a • v) y =
      (a * a) • chartChristoffelContraction (I := I) g α v v y := by
  classical
  unfold chartChristoffelContraction
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [smul_smul]
  congr 1
  calc ∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i (a • v) * chartCoord (E := E) j (a • v)
      = ∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
          (a * chartCoord (E := E) i v) * (a * chartCoord (E := E) j v) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [chartCoord_smul, chartCoord_smul]
    _ = (a * a) * ∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i v * chartCoord (E := E) j v := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        ring

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The Christoffel contraction is even in its (repeated) velocity slot:
negating the velocity vector leaves `Γ(v, v)(y)` unchanged. This is the
key sign cancellation behind time-reversal invariance of the geodesic
equation, where the velocity flips sign but the acceleration does not. -/
lemma chartChristoffelContraction_neg
    (g : RiemannianMetric I M) (α : M) (v : E) (y : E) :
    chartChristoffelContraction (I := I) g α (-v) (-v) y =
      chartChristoffelContraction (I := I) g α v v y := by
  have hneg : (-v : E) = ((-1 : ℝ) • v) := (neg_one_smul ℝ v).symm
  rw [hneg, chartChristoffelContraction_smul_smul (I := I) g α (-1 : ℝ) v y]
  norm_num

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Additivity of the Christoffel contraction in its second vector slot:
`Γ(u, v + w)(y) = Γ(u, v)(y) + Γ(u, w)(y)`. -/
lemma chartChristoffelContraction_add_right (g : RiemannianMetric I M) (α : M)
    (u v w : E) (y : E) :
    chartChristoffelContraction (I := I) g α u (v + w) y =
      chartChristoffelContraction (I := I) g α u v y
      + chartChristoffelContraction (I := I) g α u w y := by
  classical
  unfold chartChristoffelContraction
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← add_smul]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [chartCoord_add]
  ring

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Homogeneity of the Christoffel contraction in its second vector slot:
`Γ(u, a • w)(y) = a • Γ(u, w)(y)`. -/
lemma chartChristoffelContraction_smul_right (g : RiemannianMetric I M) (α : M)
    (u : E) (a : ℝ) (w : E) (y : E) :
    chartChristoffelContraction (I := I) g α u (a • w) y =
      a • chartChristoffelContraction (I := I) g α u w y := by
  classical
  unfold chartChristoffelContraction
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_smul]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [chartCoord_smul]
  ring

/-- **Math.** The geodesic vector field on the tangent bundle, written in the
canonical chart at the foot point `p.proj`. The first component is the
fibre vector `p.2`, the second component is the negation of the
Christoffel contraction of `p.2` with itself at the chart image of
`p.proj`. -/
def geodesicVectorField (g : RiemannianMetric I M)
    (p : TangentBundle I M) : TangentSpace I.tangent p :=
  (p.2, - chartChristoffelContraction (I := I) g p.proj p.2 p.2
      (extChartAt I p.proj p.proj))

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Unfolding lemma for `geodesicVectorField`. -/
@[simp] lemma geodesicVectorField_def
    (g : RiemannianMetric I M) (p : TangentBundle I M) :
    geodesicVectorField (I := I) g p =
      (p.2, - chartChristoffelContraction (I := I) g p.proj p.2 p.2
          (extChartAt I p.proj p.proj)) := rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** First component: the projection of `geodesicVectorField` onto the
horizontal `T_α M` factor returns the fibre coordinate of `p`. -/
@[simp] lemma geodesicVectorField_fst
    (g : RiemannianMetric I M) (p : TangentBundle I M) :
    (geodesicVectorField (I := I) g p).1 = p.2 := rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Second component: the projection onto the vertical factor returns
`-Γ(p.proj)(p.2, p.2)(φ_{p.proj}(p.proj))`. -/
@[simp] lemma geodesicVectorField_snd
    (g : RiemannianMetric I M) (p : TangentBundle I M) :
    (geodesicVectorField (I := I) g p).2 =
      - chartChristoffelContraction (I := I) g p.proj p.2 p.2
          (extChartAt I p.proj p.proj) := rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** At the zero section, the geodesic vector field reduces to the zero
vector in the vertical factor. The horizontal factor is still zero
because the fibre coordinate at the zero section is zero. -/
lemma geodesicVectorField_zero_section
    (g : RiemannianMetric I M) (α : M) :
    geodesicVectorField (I := I) g (⟨α, (0 : E)⟩ : TangentBundle I M) =
      ((0 : E), (0 : E)) := by
  change (((0 : E), - chartChristoffelContraction (I := I) g α (0 : E) (0 : E) _)
    : E × E) = ((0 : E), (0 : E))
  rw [chartChristoffelContraction_zero_left]
  simp

/-! ### Degree-2 fibre homogeneity of the geodesic spray

The geodesic vector field is a *second-order spray*: in coordinates it reads
`(x, v) ↦ (v, -Γ_α(v, v)(x))`.  Under fibre scaling `m_a : (x, v) ↦ (x, a·v)`
the horizontal (velocity) component scales linearly while the vertical
(acceleration) component scales quadratically, because the Christoffel
contraction is a `(2,0)`-tensor in its velocity slot
(`chartChristoffelContraction_smul_smul`).  This degree-2 homogeneity is the
coordinate heart of the geodesic homogeneity lemma `γ(t, q, a v) = γ(a t, q, v)`
(do Carmo, Ch. 3, Lemma 2.6). -/

/-- **Math.** The geodesic spray in raw chart coordinates: at a chart-image point
`x : E` and velocity coordinate `v : E` it returns `(v, -Γ_α(v, v)(x)) : E × E`.
This is the common coordinate map underlying both `geodesicVectorField`
(read in the moving chart at the foot point) and
`geodesicVectorFieldChartFiber` (read in the fixed chart at `α`). -/
def geodesicSprayCoord (g : RiemannianMetric I M) (α : M) (x v : E) : E × E :=
  (v, - chartChristoffelContraction (I := I) g α v v x)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma geodesicSprayCoord_def
    (g : RiemannianMetric I M) (α : M) (x v : E) :
    geodesicSprayCoord (I := I) g α x v =
      (v, - chartChristoffelContraction (I := I) g α v v x) := rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The moving-chart geodesic vector field is the spray coordinate map read
at the foot point's own chart. -/
lemma geodesicVectorField_eq_sprayCoord
    (g : RiemannianMetric I M) (p : TangentBundle I M) :
    geodesicVectorField (I := I) g p =
      geodesicSprayCoord (I := I) g p.proj (extChartAt I p.proj p.proj) p.2 :=
  rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Degree-2 fibre homogeneity of the geodesic spray.** Scaling the
velocity coordinate by `a` scales the horizontal component linearly and the
vertical (acceleration) component quadratically:
`S(x, a v) = (a v, a² · (S(x, v))₂)`. This is the coordinate form of the
homogeneity `d m_a ∘ (a · S) = S ∘ m_a` of the geodesic spray under fibre
scaling `m_a`, and the algebraic heart of do Carmo's homogeneity lemma 2.6. -/
lemma geodesicSprayCoord_smul_velocity
    (g : RiemannianMetric I M) (α : M) (a : ℝ) (x v : E) :
    geodesicSprayCoord (I := I) g α x (a • v) =
      (a • v, (a * a) • (geodesicSprayCoord (I := I) g α x v).2) := by
  unfold geodesicSprayCoord
  rw [chartChristoffelContraction_smul_smul (I := I) g α a v x]
  simp [smul_neg]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Degree-2 fibre homogeneity for the moving-chart geodesic vector field:
scaling the fibre vector of `p` by `a` (keeping the foot fixed) scales the
horizontal component linearly and the vertical component by `a²`. -/
lemma geodesicVectorField_fiberScale
    (g : RiemannianMetric I M) (a : ℝ) (p : TangentBundle I M) :
    geodesicVectorField (I := I) g
        (⟨p.proj, a • p.2⟩ : TangentBundle I M) =
      (a • p.2, (a * a) • (geodesicVectorField (I := I) g p).2) := by
  rw [geodesicVectorField_eq_sprayCoord, geodesicVectorField_eq_sprayCoord]
  exact geodesicSprayCoord_smul_velocity (I := I) g p.proj a
    (extChartAt I p.proj p.proj) p.2

/-- **Math.** Auxiliary: the chart-local curve `s ↦ φ_{γ t}(γ s)` for a fixed
"base time" `t`. The chart is centred at `γ t` so the predicate below
checks the second-derivative equation in the canonical chart at the
point traversed at time `t`. -/
def chartLocalCurve (γ : ℝ → M) (t : ℝ) : ℝ → E :=
  fun s => extChartAt I (γ t) (γ s)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
@[simp] lemma chartLocalCurve_def (γ : ℝ → M) (t s : ℝ) :
    chartLocalCurve (I := I) γ t s = extChartAt I (γ t) (γ s) := rfl

/-- **Math.** The geodesic equation, expressed at a single base time `t`. There
exist a velocity vector `v : E` and an acceleration vector `a : E` such
that, in the chart at `γ t`:
* the chart curve `s ↦ φ_{γ t}(γ s)` has derivative `v` at `s = t`;
* the chart curve has, in addition, a derivative of its derivative at
  `s = t` equal to `a`;
* the geodesic identity `a + Γ_{γ t}(v, v)(φ_{γ t}(γ t)) = 0` holds. -/
def HasGeodesicEquationAt (g : RiemannianMetric I M) (γ : ℝ → M)
    (t : ℝ) : Prop :=
  ∃ v a : E,
    HasDerivAt (chartLocalCurve (I := I) γ t) v t ∧
    (∀ᶠ s in nhds t, HasDerivAt (chartLocalCurve (I := I) γ t)
        (deriv (chartLocalCurve (I := I) γ t) s) s) ∧
    HasDerivAt (fun s => deriv (chartLocalCurve (I := I) γ t) s) a t ∧
    a + chartChristoffelContraction (I := I) g (γ t) v v
        (extChartAt I (γ t) (γ t)) = 0

/-- **Math.** The chart-α coordinate of the fibre vector of `p : TangentBundle I M`. -/
def chartFiberCoord (α : M) (p : TangentBundle I M) : E :=
  (trivializationAt E (TangentSpace I) α p).2

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartFiberCoord_def (α : M) (p : TangentBundle I M) :
    chartFiberCoord (I := I) α p =
      (trivializationAt E (TangentSpace I) α p).2 := rfl

/-- **Math.** The fiber-coordinate expression of the geodesic vector field at `p`,
written in the chart at the FIXED basepoint `α`. The first factor is the
chart-α coordinate of the fibre vector; the second is the negation of the
Christoffel contraction of that coordinate with itself, evaluated at the
chart image of `p.proj` through the chart at `α`. -/
def geodesicVectorFieldChartFiber (g : RiemannianMetric I M) (α : M)
    (p : TangentBundle I M) : E × E :=
  let v := chartFiberCoord (I := I) α p
  (v, - chartChristoffelContraction (I := I) g α v v
    (extChartAt I α p.proj))

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma geodesicVectorFieldChartFiber_def
    (g : RiemannianMetric I M) (α : M) (p : TangentBundle I M) :
    geodesicVectorFieldChartFiber (I := I) g α p =
      let v := chartFiberCoord (I := I) α p
      (v, - chartChristoffelContraction (I := I) g α v v
        (extChartAt I α p.proj)) := rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The fixed-chart-`α` geodesic vector field fibre is the spray coordinate
map read at the chart image of the foot and the chart-`α` fibre coordinate.
Together with `geodesicSprayCoord_smul_velocity`, this gives the degree-2
fibre homogeneity of the integral-curve geodesic vector field directly in the
coordinates in which the geodesic ODE is written. -/
lemma geodesicVectorFieldChartFiber_eq_sprayCoord
    (g : RiemannianMetric I M) (α : M) (p : TangentBundle I M) :
    geodesicVectorFieldChartFiber (I := I) g α p =
      geodesicSprayCoord (I := I) g α (extChartAt I α p.proj)
        (chartFiberCoord (I := I) α p) :=
  rfl

/-- **Math.** The geodesic vector field in chart-fixed form, viewed as a section of
`T(TM)`. By construction, the value at `p` lies in `TangentSpace I.tangent p`
(which is definitionally `E × E`); it is built so that the trivialisation of
`T(TM)` at `⟨α, (0 : E)⟩` sends it back to `geodesicVectorFieldChartFiber g α p`.
-/
def geodesicVectorFieldChart (g : RiemannianMetric I M) (α : M)
    (p : TangentBundle I M) : TangentSpace I.tangent p :=
  (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).symm p
    (geodesicVectorFieldChartFiber (I := I) g α p)

/-- **Math.** The open set in `TangentBundle I M` on which the chart-fixed geodesic
vector field is smooth: the preimage of `(chartAt H α).source` under the
projection. -/
def geodesicChartDomain (α : M) : Set (TangentBundle I M) :=
  (Bundle.TotalSpace.proj : TangentBundle I M → M) ⁻¹' (chartAt H α).source

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma geodesicChartDomain_isOpen (α : M) :
    IsOpen (geodesicChartDomain (I := I) (M := M) α) :=
  (chartAt H α).open_source.preimage (FiberBundle.continuous_proj E (TangentSpace I))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
lemma mem_geodesicChartDomain_of_proj {α : M} {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) : p ∈ geodesicChartDomain (I := I) α :=
  hp

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
lemma proj_mem_chartAt_source_of_mem_geodesicChartDomain {α : M}
    {p : TangentBundle I M} (hp : p ∈ geodesicChartDomain (I := I) α) :
    p.proj ∈ (chartAt H α).source := hp

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The chart-α domain coincides with the base set of the trivialisation of
`T(TM)` at `⟨α, 0⟩`: both are the set of `p : TM` with `p.proj` in
`(chartAt H α).source`. -/
lemma geodesicChartDomain_eq_trivBaseSet (α : M) :
    geodesicChartDomain (I := I) α =
      (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).baseSet := by
  classical
  unfold geodesicChartDomain
  ext p
  rw [Set.mem_preimage,
    TangentBundle.trivializationAt_baseSet (I := I.tangent)
      (M := TangentBundle I M) (⟨α, (0 : E)⟩ : TangentBundle I M)]
  exact (TangentBundle.mem_chart_source_iff (I := I) (M := M) p
    (⟨α, (0 : E)⟩ : TangentBundle I M)).symm

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** At the zero section, `chartFiberCoord α ⟨α, 0⟩ = 0`: the fibre coordinate
in the chart at `α` of the zero vector at `α` is the zero of `E`. -/
lemma chartFiberCoord_self_zero (α : M) :
    chartFiberCoord (I := I) α
      (⟨α, (0 : E)⟩ : TangentBundle I M) = 0 := by
  classical
  have hα : α ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' α
  have hzero := (trivializationAt E (TangentSpace I) α).zeroSection ℝ (x := α) hα
  have hzero' : (trivializationAt E (TangentSpace I) α)
      (⟨α, (0 : TangentSpace I α)⟩ : TangentBundle I M) = (α, 0) := hzero
  change (trivializationAt E (TangentSpace I) α
      (⟨α, (0 : TangentSpace I α)⟩ : TangentBundle I M)).2 = 0
  rw [hzero']

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The chart-fixed geodesic vector field at `⟨α, 0⟩` (chart basepoint = foot
point, zero velocity) is the zero element of `TangentSpace I.tangent ⟨α, 0⟩`. -/
lemma geodesicVectorFieldChart_zero_section
    (g : RiemannianMetric I M) (α : M) :
    geodesicVectorFieldChart (I := I) g α
        (⟨α, (0 : E)⟩ : TangentBundle I M) = 0 := by
  classical
  have hcf : chartFiberCoord (I := I) α
      (⟨α, (0 : E)⟩ : TangentBundle I M) = 0 :=
    chartFiberCoord_self_zero (I := I) α
  have hfiber : geodesicVectorFieldChartFiber (I := I) g α
      (⟨α, (0 : E)⟩ : TangentBundle I M) = (0, 0) := by
    change (chartFiberCoord (I := I) α (⟨α, (0 : E)⟩ : TangentBundle I M),
        - chartChristoffelContraction (I := I) g α
            (chartFiberCoord (I := I) α (⟨α, (0 : E)⟩ : TangentBundle I M))
            (chartFiberCoord (I := I) α (⟨α, (0 : E)⟩ : TangentBundle I M))
            (extChartAt I α (⟨α, (0 : E)⟩ : TangentBundle I M).proj)) = (0, 0)
    rw [hcf, chartChristoffelContraction_zero_left, neg_zero]
  unfold geodesicVectorFieldChart
  rw [hfiber]
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)
  have hcoe := Bundle.Trivialization.coe_symmₗ (R := ℝ) e
    (⟨α, (0 : E)⟩ : TangentBundle I M)
  have : e.symm (⟨α, (0 : E)⟩ : TangentBundle I M) (0 : E × E) = 0 := by
    have h := congrFun hcoe (0 : E × E)
    rw [← h]
    exact map_zero _
  exact this

/-- **Math.** Local geodesic at time `t₀`: there is a basepoint `α : M` and a lifted
curve `f : ℝ → TangentBundle I M` with `(f t).proj = γ t` for all `t`,
whose foot at `t₀` lies in the basepoint chart-source
`(chartAt H α).source`, such that `f` is a local integral curve of the
chart-fixed geodesic vector field `geodesicVectorFieldChart g α` at `t₀`.

The foot-in-source clause `(f t₀).proj ∈ (chartAt H α).source` records that
the lift's foot at `t₀` lies in the chart at the basepoint `α`. This is
where the chart-fixed geodesic vector field is genuinely the geodesic
spray (off the chart-source it degenerates to the zero section), so it is
the natural well-posedness condition for the witness. Every constructor
(Picard–Lindelöf at the initial point, the stationary geodesic, and the
chart-rebased maximal-interval witnesses) supplies it; consumers use it to
transfer the integral-curve property to the foot's own chart. -/
def IsGeodesicAt (g : RiemannianMetric I M) (γ : ℝ → M)
    (t₀ : ℝ) : Prop :=
  ∃ (α : M) (f : ℝ → TangentBundle I M),
    (∀ t, (f t).proj = γ t) ∧
    (f t₀).proj ∈ (chartAt H α).source ∧
    IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t₀

/-- **Math.** A curve `γ : ℝ → M` is a geodesic of `g` if it satisfies the intrinsic
moving-foot geodesic equation `HasGeodesicEquationAt g γ t` at every time
`t`. This is the chart-independent definition: at each time `t` the
equation is read in the canonical chart centred at the foot point `γ t`,
so it remains meaningful for geodesics leaving any single chart. -/
def IsGeodesic (g : RiemannianMetric I M) (γ : ℝ → M) : Prop :=
  ∀ t : ℝ, HasGeodesicEquationAt (I := I) g γ t

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** A global geodesic satisfies the moving-foot geodesic equation at every
time (definitional projection). -/
lemma IsGeodesic.hasGeodesicEquationAt {g : RiemannianMetric I M}
    {γ : ℝ → M} (hγ : IsGeodesic (I := I) g γ) (t : ℝ) :
    HasGeodesicEquationAt (I := I) g γ t :=
  hγ t

/-- **Math.** `γ : ℝ → M` is a geodesic of `g` on `s : Set ℝ` if it satisfies the
intrinsic moving-foot geodesic equation `HasGeodesicEquationAt g γ t` at
every time `t ∈ s`. The set-relativised analogue of `IsGeodesic`. -/
def IsGeodesicOn (g : RiemannianMetric I M) (γ : ℝ → M)
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasGeodesicEquationAt (I := I) g γ t

/-- **Math.** A **geodesic curve** is a continuous curve satisfying the intrinsic
moving-foot geodesic equation at every time.  Continuity is part of the public
notion: `HasGeodesicEquationAt` reads through junk-extended charts and does not,
by itself, imply continuity. -/
def IsGeodesicCurve (g : RiemannianMetric I M) (γ : ℝ → M) : Prop :=
  Continuous γ ∧ IsGeodesic (I := I) g γ

/-- **Math.** A continuous geodesic curve on a set of parameter values. -/
def IsGeodesicCurveOn (g : RiemannianMetric I M) (γ : ℝ → M)
    (s : Set ℝ) : Prop :=
  ContinuousOn γ s ∧ IsGeodesicOn (I := I) g γ s

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma IsGeodesicCurve.continuous {g : RiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesicCurve (I := I) g γ) : Continuous γ :=
  hγ.1

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma IsGeodesicCurve.isGeodesic {g : RiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesicCurve (I := I) g γ) : IsGeodesic (I := I) g γ :=
  hγ.2

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma IsGeodesicCurve.isGeodesicCurveOn {g : RiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesicCurve (I := I) g γ) (s : Set ℝ) :
    IsGeodesicCurveOn (I := I) g γ s :=
  ⟨hγ.1.continuousOn, fun t _ ↦ hγ.2 t⟩

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma IsGeodesicCurveOn.mono {g : RiemannianMetric I M} {γ : ℝ → M}
    {s t : Set ℝ} (hγ : IsGeodesicCurveOn (I := I) g γ s) (ht : t ⊆ s) :
    IsGeodesicCurveOn (I := I) g γ t :=
  ⟨hγ.1.mono ht, fun u hu ↦ hγ.2 u (ht hu)⟩

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** A geodesic on a set satisfies the moving-foot geodesic equation at
every time of the set (definitional projection). -/
lemma IsGeodesicOn.hasGeodesicEquationAt {g : RiemannianMetric I M}
    {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hγ : IsGeodesicOn (I := I) g γ s) (ht : t ∈ s) :
    HasGeodesicEquationAt (I := I) g γ t :=
  hγ t ht

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** `IsGeodesicOn` is monotone in the set. -/
lemma IsGeodesicOn.mono {g : RiemannianMetric I M}
    {γ : ℝ → M} {s s' : Set ℝ}
    (hγ : IsGeodesicOn (I := I) g γ s) (hs : s' ⊆ s) :
    IsGeodesicOn (I := I) g γ s' :=
  fun t ht => hγ t (hs ht)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** A global geodesic, restricted to any set, is a geodesic on that set. -/
lemma IsGeodesic.isGeodesicOn {g : RiemannianMetric I M}
    {γ : ℝ → M} (hγ : IsGeodesic (I := I) g γ) (s : Set ℝ) :
    IsGeodesicOn (I := I) g γ s :=
  fun t _ => hγ t

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The constant curve `fun _ => p` is a geodesic. In the chart at `p`,
the chart-local curve `s ↦ φ_p p` is constant, so both its velocity and
acceleration vanish, and the Christoffel contraction of the zero velocity
with itself vanishes by `chartChristoffelContraction_zero_left`. -/
theorem isGeodesic_const (g : RiemannianMetric I M) (p : M) :
    IsGeodesic (I := I) g (fun _ : ℝ => p) := by
  classical
  intro t
  have hconst : chartLocalCurve (I := I) (fun _ : ℝ => p) t =
      fun _ : ℝ => extChartAt I p p := by
    funext s; rfl
  refine ⟨(0 : E), (0 : E), ?_, ?_, ?_, ?_⟩
  · rw [hconst]; exact hasDerivAt_const t (extChartAt I p p)
  · refine Filter.Eventually.of_forall (fun s => ?_)
    rw [hconst]
    have hd : deriv (fun _ : ℝ => extChartAt I p p) s = 0 := deriv_const s _
    rw [hd]; exact hasDerivAt_const s (extChartAt I p p)
  · have hd : (fun s => deriv (chartLocalCurve (I := I) (fun _ : ℝ => p) t) s)
        = fun _ : ℝ => (0 : E) := by
      funext s; rw [hconst]; exact deriv_const s _
    rw [hd]; exact hasDerivAt_const t (0 : E)
  · rw [chartChristoffelContraction_zero_left]
    simp

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** A constant curve is a local geodesic at every time (spray formulation).
The constant lift `fun _ => ⟨p, 0⟩` is an integral curve of the chart-fixed
geodesic vector field, which vanishes at the zero section. -/
theorem IsGeodesicAt.const (g : RiemannianMetric I M) (p : M) (t : ℝ) :
    IsGeodesicAt (I := I) g (fun _ : ℝ => p) t := by
  classical
  refine ⟨p, fun _ : ℝ => (⟨p, (0 : E)⟩ : TangentBundle I M), fun _ => rfl,
    mem_chart_source H p, ?_⟩
  refine (isMIntegralCurve_const ?_).isMIntegralCurveAt t
  exact geodesicVectorFieldChart_zero_section (I := I) g p

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Time-translation reparametrisation preserves the geodesic property.
At time `t`, the chart-local curve of `s ↦ γ (s + b)` is the chart-local
curve of `γ` at the shifted base time `t + b`, precomposed with the shift
`s ↦ s + b`; the geodesic equation transfers under the shift since
`HasDerivAt.comp_add_const` carries derivatives unchanged and the foot
point `γ (t + b)` and velocity coincide. -/
theorem isGeodesic_comp_add
    {g : RiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) (b : ℝ) :
    IsGeodesic (I := I) g (fun s => γ (s + b)) := by
  intro t
  obtain ⟨v, a, hv, hev, ha, hgeo⟩ := hγ (t + b)
  have hshift : chartLocalCurve (I := I) (fun s => γ (s + b)) t =
      fun s => chartLocalCurve (I := I) γ (t + b) (s + b) := by
    funext s; rfl
  refine ⟨v, a, ?_, ?_, ?_, ?_⟩
  · rw [hshift]
    exact hv.comp_add_const t b
  · rw [hshift]
    have hderiv : ∀ s,
        deriv (fun s => chartLocalCurve (I := I) γ (t + b) (s + b)) s =
          deriv (chartLocalCurve (I := I) γ (t + b)) (s + b) := by
      intro s
      exact deriv_comp_add_const (chartLocalCurve (I := I) γ (t + b)) b s
    have hev' : ∀ᶠ s in nhds t, HasDerivAt
        (chartLocalCurve (I := I) γ (t + b))
        (deriv (chartLocalCurve (I := I) γ (t + b)) (s + b)) (s + b) := by
      have hcont : Filter.Tendsto (fun s : ℝ => s + b) (nhds t) (nhds (t + b)) :=
        (continuous_add_const b).continuousAt
      exact hcont.eventually hev
    filter_upwards [hev'] with s hs
    rw [hderiv s]
    exact hs.comp_add_const s b
  · rw [hshift]
    have hd2 : (fun s => deriv
        (fun s => chartLocalCurve (I := I) γ (t + b) (s + b)) s) =
        fun s => deriv (chartLocalCurve (I := I) γ (t + b)) (s + b) := by
      funext s
      exact deriv_comp_add_const (chartLocalCurve (I := I) γ (t + b)) b s
    rw [hd2]
    exact ha.comp_add_const t b
  · exact hgeo

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
/-- **Math.** The chart-local curve of the time-reversed curve `s ↦ γ (-s)` at base
time `τ` equals the chart-local curve of `γ` at the reflected base time
`-τ`, precomposed with negation: `chartLocalCurve (γ ∘ neg) τ = u ∘ neg`
where `u = chartLocalCurve γ (-τ)`. Holds definitionally. -/
lemma chartLocalCurve_comp_neg (γ : ℝ → M) (τ : ℝ) :
    chartLocalCurve (I := I) (fun s => γ (-s)) τ =
      (fun s => chartLocalCurve (I := I) γ (-τ) (-s)) := rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Pointwise time-reversal of the geodesic equation.** If `γ` satisfies
the moving-foot geodesic equation at `-τ`, then the time-reversed curve
`s ↦ γ (-s)` satisfies it at `τ`. The reversed-curve velocity is the
negation of the original velocity at `-τ`; the acceleration is unchanged;
and the Christoffel contraction is even in the velocity, so the geodesic
identity carries over unchanged. -/
theorem hasGeodesicEquationAt_comp_neg
    {g : RiemannianMetric I M} {γ : ℝ → M} {τ : ℝ}
    (hγ : HasGeodesicEquationAt (I := I) g γ (-τ)) :
    HasGeodesicEquationAt (I := I) g (fun s => γ (-s)) τ := by
  obtain ⟨v, a, hv, hev, ha, hgeo⟩ := hγ
  set u : ℝ → E := chartLocalCurve (I := I) γ (-τ) with hu_def
  have hrev : chartLocalCurve (I := I) (fun s => γ (-s)) τ = (fun s => u (-s)) :=
    chartLocalCurve_comp_neg (I := I) γ τ
  have hderiv_rev : deriv (chartLocalCurve (I := I) (fun s => γ (-s)) τ) =
      (fun s => -(deriv u (-s))) := by
    rw [hrev]; funext s; exact deriv_comp_neg u s
  refine ⟨-v, a, ?_, ?_, ?_, ?_⟩
  · rw [hrev]
    have hcomp : HasDerivAt (fun s => u (-s)) ((-1 : ℝ) • v) τ := by
      have := (hv.scomp τ (hasDerivAt_neg τ))
      simpa [Function.comp_def] using this
    simpa using hcomp
  · rw [hderiv_rev, hrev]
    have hcont : Filter.Tendsto (fun s : ℝ => -s) (nhds τ) (nhds (-τ)) :=
      (continuous_neg.tendsto τ)
    have hev' : ∀ᶠ s in nhds τ,
        HasDerivAt u (deriv u (-s)) (-s) := hcont.eventually hev
    filter_upwards [hev'] with s hs
    have := hs.scomp s (hasDerivAt_neg s)
    simpa [Function.comp_def] using this
  · rw [hderiv_rev]
    have hinner : HasDerivAt (fun s => deriv u (-s)) ((-1 : ℝ) • a) τ := by
      have := (ha.scomp τ (hasDerivAt_neg τ))
      simpa [Function.comp_def] using this
    have hfin := hinner.neg
    simpa using hfin
  · rw [chartChristoffelContraction_neg (I := I) g _ v]
    exact hgeo

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Time-reversal of a global geodesic.** If `γ` is a geodesic, so is its
time reversal `s ↦ γ (-s)`. -/
theorem isGeodesic_comp_neg
    {g : RiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) :
    IsGeodesic (I := I) g (fun s => γ (-s)) := by
  intro τ
  exact hasGeodesicEquationAt_comp_neg (I := I) (hγ (-τ))

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Time-reversal of a geodesic on a set.** If `γ` is a geodesic on
`s : Set ℝ`, then the time reversal `t ↦ γ (-t)` is a geodesic on the
preimage `Neg.neg ⁻¹' s = {τ | -τ ∈ s}`. -/
theorem isGeodesicOn_comp_neg
    {g : RiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ}
    (hγ : IsGeodesicOn (I := I) g γ s) :
    IsGeodesicOn (I := I) g (fun t => γ (-t)) (Neg.neg ⁻¹' s) := by
  intro τ hτ
  exact hasGeodesicEquationAt_comp_neg (I := I) (hγ (-τ) hτ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
/-- **Math.** The chart-local curve of the affinely rescaled curve `s ↦ γ (a·s)` at
base time `τ` equals the chart-local curve of `γ` at the rescaled base time
`a·τ`, precomposed with multiplication by `a`. Holds definitionally, since
both sides read `γ (a·s)` in the chart centred at the common foot
`γ (a·τ)`. -/
lemma chartLocalCurve_comp_mul_left (γ : ℝ → M) (a τ : ℝ) :
    chartLocalCurve (I := I) (fun s => γ (a * s)) τ =
      (fun s => chartLocalCurve (I := I) γ (a * τ) (a * s)) := rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Pointwise affine rescaling of the geodesic equation (do Carmo Ch. 3,
Lemma 2.6, core).** If `γ` satisfies the moving-foot geodesic equation at
`a·τ`, then the rescaled curve `s ↦ γ (a·s)` satisfies it at `τ`. The
rescaled velocity is `a·v`, the acceleration is `a²·acc`, and since the
Christoffel contraction scales as a `(2,0)`-tensor
(`chartChristoffelContraction_smul_smul`), the geodesic identity carries
over with the common factor `a²`. This is the reparametrisation heart of
the homogeneity lemma `γ(t, q, a v) = γ(a t, q, v)`. -/
theorem hasGeodesicEquationAt_comp_mul_left
    {g : RiemannianMetric I M} {γ : ℝ → M} {a τ : ℝ}
    (hγ : HasGeodesicEquationAt (I := I) g γ (a * τ)) :
    HasGeodesicEquationAt (I := I) g (fun s => γ (a * s)) τ := by
  obtain ⟨v, acc, hv, hev, ha, hgeo⟩ := hγ
  set u : ℝ → E := chartLocalCurve (I := I) γ (a * τ) with hu_def
  have hrev : chartLocalCurve (I := I) (fun s => γ (a * s)) τ = (fun s => u (a * s)) :=
    chartLocalCurve_comp_mul_left (I := I) γ a τ
  have hderiv_rev : deriv (chartLocalCurve (I := I) (fun s => γ (a * s)) τ) =
      (fun s => a • deriv u (a * s)) := by
    rw [hrev]; funext s; exact deriv_comp_mul_left a u s
  refine ⟨a • v, (a * a) • acc, ?_, ?_, ?_, ?_⟩
  · rw [hrev]
    have := hv.scomp τ (hasDerivAt_const_mul a)
    simpa [Function.comp_def] using this
  · rw [hderiv_rev, hrev]
    have hcont : Filter.Tendsto (fun s : ℝ => a * s) (nhds τ) (nhds (a * τ)) :=
      (continuous_const.mul continuous_id).tendsto τ
    have hev' : ∀ᶠ s in nhds τ,
        HasDerivAt u (deriv u (a * s)) (a * s) := hcont.eventually hev
    filter_upwards [hev'] with s hs
    have := hs.scomp s (hasDerivAt_const_mul a)
    simpa [Function.comp_def] using this
  · rw [hderiv_rev]
    have hcomp : HasDerivAt (fun s => deriv u (a * s)) (a • acc) τ := by
      have := ha.scomp τ (hasDerivAt_const_mul a)
      simpa [Function.comp_def] using this
    have hfin := hcomp.const_smul a
    simpa [smul_smul] using hfin
  · show (a * a) • acc + chartChristoffelContraction (I := I) g (γ (a * τ))
        (a • v) (a • v) (extChartAt I (γ (a * τ)) (γ (a * τ))) = 0
    rw [chartChristoffelContraction_smul_smul (I := I) g (γ (a * τ)) a v,
      ← smul_add, hgeo, smul_zero]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Affine rescaling of a global geodesic.** If `γ` is a geodesic, so is
its affine reparametrisation `s ↦ γ (a·s)` for any `a : ℝ`. Together with
the velocity scaling `(γ ∘ (a·))'(t) = a · γ'(a t)`, this is do Carmo's
homogeneity lemma 2.6: `γ(t, q, a v) = γ(a t, q, v)`. -/
theorem isGeodesic_comp_mul_left
    {g : RiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) (a : ℝ) :
    IsGeodesic (I := I) g (fun s => γ (a * s)) := by
  intro τ
  exact hasGeodesicEquationAt_comp_mul_left (I := I) (hγ (a * τ))

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Affine rescaling of a geodesic on a set.** If `γ` is a geodesic on
`s : Set ℝ`, then `t ↦ γ (a·t)` is a geodesic on the preimage
`(a * ·) ⁻¹' s = {τ | a·τ ∈ s}`. -/
theorem isGeodesicOn_comp_mul_left
    {g : RiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ} {a : ℝ}
    (hγ : IsGeodesicOn (I := I) g γ s) :
    IsGeodesicOn (I := I) g (fun t => γ (a * t)) ((fun t => a * t) ⁻¹' s) := by
  intro τ hτ
  exact hasGeodesicEquationAt_comp_mul_left (I := I) (hγ (a * τ) hτ)

section ChartFixedSmoothness

variable [I.Boundaryless]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** The trivialisation source is the preimage of the chart base set under the
projection. Specialised to the tangent bundle at `α`. -/
lemma trivializationAt_source_eq (α : M) :
    (trivializationAt E (TangentSpace I) α).source =
      geodesicChartDomain (I := I) (M := M) α := by
  rw [Trivialization.source_eq]; rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** The chart-α coordinate `chartFiberCoord α : TangentBundle I M → E` is smooth
on `geodesicChartDomain α`. Equivalent to: the second component of the
trivialisation of `TM` at `α` is smooth on the chart base set. -/
lemma chartFiberCoord_contMDiffOn (α : M) :
    ContMDiffOn I.tangent 𝓘(ℝ, E) ∞
      (chartFiberCoord (I := I) (α := α)) (geodesicChartDomain (I := I) α) := by
  classical
  have he : MapsTo (id : TangentBundle I M → TangentBundle I M)
      (geodesicChartDomain (I := I) α)
      (trivializationAt E (TangentSpace I) α).source := by
    rw [trivializationAt_source_eq (I := I) α]
    intro p hp; exact hp
  have hiff :=
    (trivializationAt E (TangentSpace I) α).contMDiffOn_iff
      (IM := I.tangent) (IB := I) (n := (∞ : WithTop ℕ∞))
      (f := id) (s := geodesicChartDomain (I := I) α) he
  have hid : ContMDiffOn I.tangent (I.prod 𝓘(ℝ, E)) ∞
      (id : TangentBundle I M → TangentBundle I M)
      (geodesicChartDomain (I := I) α) := contMDiffOn_id
  exact (hiff.mp hid).2

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** Projection `TangentBundle I M → M` is globally smooth (Mathlib fact, repeated
here in a `ContMDiffOn` form for convenience). -/
lemma proj_contMDiffOn (s : Set (TangentBundle I M)) :
    ContMDiffOn I.tangent I ∞
      (Bundle.TotalSpace.proj : TangentBundle I M → M) s :=
  (Bundle.contMDiff_proj (TangentSpace I) (n := (∞ : WithTop ℕ∞))).contMDiffOn

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** The composition `extChartAt I α ∘ proj : TangentBundle I M → E` is smooth on
the chart domain. -/
lemma extChartAt_proj_contMDiffOn (α : M) :
    ContMDiffOn I.tangent 𝓘(ℝ, E) ∞
      (fun p : TangentBundle I M => extChartAt I α p.proj)
      (geodesicChartDomain (I := I) α) := by
  classical
  have hproj : ContMDiffOn I.tangent I ∞
      (Bundle.TotalSpace.proj : TangentBundle I M → M)
      (geodesicChartDomain (I := I) α) :=
    proj_contMDiffOn (I := I) (M := M) _
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source := contMDiffOn_extChartAt
  have hsubset : geodesicChartDomain (I := I) α ⊆
      Bundle.TotalSpace.proj ⁻¹' (chartAt H α).source :=
    fun _ hp => hp
  exact hchart.comp hproj hsubset

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The chart Christoffel symbol entry `chartChristoffel g α i j k`, evaluated at
the chart image of `p.proj`, is smooth in `p` on the chart domain. -/
lemma chartChristoffel_extChartAt_proj_contMDiffOn
    (g : RiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I.tangent 𝓘(ℝ) ∞
      (fun p : TangentBundle I M =>
        chartChristoffel (I := I) g α i j k (extChartAt I α p.proj))
      (geodesicChartDomain (I := I) α) := by
  classical
  intro p hp
  have hp_src : p.proj ∈ (chartAt H α).source := hp
  have hp_ext_src : p.proj ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hp_src
  have hp_target : extChartAt I α p.proj ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hp_ext_src
  have hp_int : extChartAt I α p.proj ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hp_target
  set Γ : E → ℝ := chartChristoffel (I := I) g α i j k with hΓ_eq
  have hΓ_on : ContDiffOn ℝ ∞ Γ (interior (extChartAt I α).target) :=
    chartChristoffel_contDiffOn_interior (I := I) g α i j k
  have hΓ_at : ContDiffAt ℝ ∞ Γ (extChartAt I α p.proj) :=
    hΓ_on.contDiffAt (isOpen_interior.mem_nhds hp_int)
  have hbase : ContMDiffWithinAt I.tangent 𝓘(ℝ, E) ∞
      (fun q : TangentBundle I M => extChartAt I α q.proj)
      (geodesicChartDomain (I := I) α) p :=
    extChartAt_proj_contMDiffOn (I := I) α p hp
  have := (hΓ_at.contMDiffAt).comp_contMDiffWithinAt p hbase
  exact this

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The Christoffel-contraction scalar
`∑_{ij} Γ^k_{ij}(y) · v_i · v_j` (with `v = chartFiberCoord α p` and
`y = extChartAt I α p.proj`) is smooth in `p` on the chart domain. -/
lemma chartChristoffelContraction_scalarCoeff_contMDiffOn
    (g : RiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I.tangent 𝓘(ℝ) ∞
      (fun p : TangentBundle I M =>
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j k (extChartAt I α p.proj) *
            chartCoord (E := E) i (chartFiberCoord (I := I) α p) *
            chartCoord (E := E) j (chartFiberCoord (I := I) α p))
      (geodesicChartDomain (I := I) α) := by
  classical
  refine contMDiffOn_finsetSum (fun i _ => ?_)
  refine contMDiffOn_finsetSum (fun j _ => ?_)
  have hΓ : ContMDiffOn I.tangent 𝓘(ℝ) ∞
      (fun p : TangentBundle I M =>
        chartChristoffel (I := I) g α i j k (extChartAt I α p.proj))
      (geodesicChartDomain (I := I) α) :=
    chartChristoffel_extChartAt_proj_contMDiffOn (I := I) g α i j k
  have hv : ContMDiffOn I.tangent 𝓘(ℝ, E) ∞
      (chartFiberCoord (I := I) (α := α)) (geodesicChartDomain (I := I) α) :=
    chartFiberCoord_contMDiffOn (I := I) α
  have hCLM_i : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (((Module.finBasis ℝ E).coord i).toContinuousLinearMap) :=
    (((Module.finBasis ℝ E).coord i).toContinuousLinearMap).contMDiff
  have hCLM_j : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (((Module.finBasis ℝ E).coord j).toContinuousLinearMap) :=
    (((Module.finBasis ℝ E).coord j).toContinuousLinearMap).contMDiff
  have hci : ContMDiffOn I.tangent 𝓘(ℝ) ∞
      (fun p : TangentBundle I M => chartCoord (E := E) i (chartFiberCoord (I := I) α p))
      (geodesicChartDomain (I := I) α) := by
    intro p hp
    exact (hCLM_i.contMDiffAt).comp_contMDiffWithinAt _ (hv p hp)
  have hcj : ContMDiffOn I.tangent 𝓘(ℝ) ∞
      (fun p : TangentBundle I M => chartCoord (E := E) j (chartFiberCoord (I := I) α p))
      (geodesicChartDomain (I := I) α) := by
    intro p hp
    exact (hCLM_j.contMDiffAt).comp_contMDiffWithinAt _ (hv p hp)
  exact (hΓ.mul hci).mul hcj

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The Christoffel-contraction `Γ_α(v, v)(y)` (with `v = chartFiberCoord α p`,
`y = extChartAt I α p.proj`) is smooth in `p` on the chart domain. -/
lemma chartChristoffelContraction_chartFiber_contMDiffOn
    (g : RiemannianMetric I M) (α : M) :
    ContMDiffOn I.tangent 𝓘(ℝ, E) ∞
      (fun p : TangentBundle I M =>
        chartChristoffelContraction (I := I) g α
          (chartFiberCoord (I := I) α p)
          (chartFiberCoord (I := I) α p)
          (extChartAt I α p.proj))
      (geodesicChartDomain (I := I) α) := by
  classical
  unfold chartChristoffelContraction
  refine contMDiffOn_finsetSum (fun k _ => ?_)
  have hscalar := chartChristoffelContraction_scalarCoeff_contMDiffOn (I := I) g α k
  have hconst : ContMDiffOn I.tangent 𝓘(ℝ, E) ∞
      (fun _ : TangentBundle I M => (Module.finBasis ℝ E) k)
      (geodesicChartDomain (I := I) α) := contMDiffOn_const
  exact hscalar.smul hconst

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The chart-fiber expression of the geodesic vector field is smooth as a
function `TangentBundle I M → E × E` on the chart domain. -/
lemma geodesicVectorFieldChartFiber_contMDiffOn
    (g : RiemannianMetric I M) (α : M) :
    ContMDiffOn I.tangent 𝓘(ℝ, E × E) ∞
      (geodesicVectorFieldChartFiber (I := I) g α)
      (geodesicChartDomain (I := I) α) := by
  classical
  have hfst : ContMDiffOn I.tangent 𝓘(ℝ, E) ∞
      (chartFiberCoord (I := I) (α := α)) (geodesicChartDomain (I := I) α) :=
    chartFiberCoord_contMDiffOn (I := I) α
  have hΓ : ContMDiffOn I.tangent 𝓘(ℝ, E) ∞
      (fun p : TangentBundle I M =>
        chartChristoffelContraction (I := I) g α
          (chartFiberCoord (I := I) α p)
          (chartFiberCoord (I := I) α p)
          (extChartAt I α p.proj))
      (geodesicChartDomain (I := I) α) :=
    chartChristoffelContraction_chartFiber_contMDiffOn (I := I) g α
  have hsnd : ContMDiffOn I.tangent 𝓘(ℝ, E) ∞
      (fun p : TangentBundle I M =>
        - chartChristoffelContraction (I := I) g α
          (chartFiberCoord (I := I) α p)
          (chartFiberCoord (I := I) α p)
          (extChartAt I α p.proj))
      (geodesicChartDomain (I := I) α) := hΓ.neg
  exact hfst.prodMk_space hsnd

/-- **Math.** The trivialisation of `T(TM)` at `⟨α, 0⟩` is in the canonical atlas, allowing
us to apply `Bundle.Trivialization.contMDiffOn_iff`. -/
private instance trivializationAt_tangent_tangent_isAtlas (α : M) :
    MemTrivializationAtlas
      (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)) :=
  ⟨FiberBundle.trivialization_mem_atlas (E × E) (TangentSpace I.tangent) _⟩

omit [I.Boundaryless] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** By construction (using the inverse trivialisation), applying the
trivialisation of `T(TM)` at `⟨α, 0⟩` to `⟨p, geodesicVectorFieldChart g α p⟩`
returns `(p, geodesicVectorFieldChartFiber g α p)` on the chart domain. -/
lemma trivializationAt_apply_geodesicVectorFieldChart
    (g : RiemannianMetric I M) (α : M)
    {p : TangentBundle I M} (hp : p ∈ geodesicChartDomain (I := I) α) :
    (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M))
      ⟨p, geodesicVectorFieldChart (I := I) g α p⟩ =
        (p, geodesicVectorFieldChartFiber (I := I) g α p) := by
  classical
  have hp' : p ∈ (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).baseSet := by
    rw [← geodesicChartDomain_eq_trivBaseSet (I := I) α]; exact hp
  exact (trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M)).apply_mk_symm hp'
      (geodesicVectorFieldChartFiber (I := I) g α p)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **G.1.2 smoothness theorem**: the chart-fixed geodesic vector field, viewed
as a section of `T(TM)`, is `C^∞` on the chart domain. -/
theorem geodesicVectorFieldChart_contMDiffOn
    (g : RiemannianMetric I M) (α : M) :
    ContMDiffOn I.tangent I.tangent.tangent ∞
      (fun p : TangentBundle I M =>
        (⟨p, geodesicVectorFieldChart (I := I) g α p⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      (geodesicChartDomain (I := I) α) := by
  classical
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M)
  have hMapsTo : MapsTo
      (fun p : TangentBundle I M =>
        (⟨p, geodesicVectorFieldChart (I := I) g α p⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      (geodesicChartDomain (I := I) α) e.source := by
    intro p hp
    rw [Trivialization.source_eq]
    rw [← geodesicChartDomain_eq_trivBaseSet (I := I) α]
    exact hp
  rw [e.contMDiffOn_iff (IM := I.tangent) (IB := I.tangent)
    (n := (∞ : WithTop ℕ∞)) hMapsTo]
  refine ⟨?_, ?_⟩
  · have hid : (fun p : TangentBundle I M =>
        (⟨p, geodesicVectorFieldChart (I := I) g α p⟩ :
          TangentBundle I.tangent (TangentBundle I M)).proj) =
        (fun p : TangentBundle I M => p) := rfl
    rw [hid]
    exact contMDiffOn_id
  · have heq : ∀ p ∈ geodesicChartDomain (I := I) α,
        (e ⟨p, geodesicVectorFieldChart (I := I) g α p⟩).2 =
          geodesicVectorFieldChartFiber (I := I) g α p := by
      intro p hp
      rw [trivializationAt_apply_geodesicVectorFieldChart (I := I) g α hp]
    have hsmooth : ContMDiffOn I.tangent 𝓘(ℝ, E × E) ∞
        (geodesicVectorFieldChartFiber (I := I) g α)
        (geodesicChartDomain (I := I) α) :=
      geodesicVectorFieldChartFiber_contMDiffOn (I := I) g α
    exact hsmooth.congr heq

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** `ContMDiffAt`-form, suitable for Mathlib's
`exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`. At every `p₀` with
`p₀.proj ∈ (chartAt H α).source`, the chart-fixed geodesic vector field is
`C^∞` (hence `C^1`). -/
theorem geodesicVectorFieldChart_contMDiffAt
    (g : RiemannianMetric I M) (α : M)
    {p₀ : TangentBundle I M}
    (hp₀ : p₀.proj ∈ (chartAt H α).source) :
    ContMDiffAt I.tangent I.tangent.tangent ∞
      (fun p : TangentBundle I M =>
        (⟨p, geodesicVectorFieldChart (I := I) g α p⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      p₀ := by
  have hop : IsOpen (geodesicChartDomain (I := I) α) :=
    geodesicChartDomain_isOpen (I := I) (M := M) α
  have hmem : p₀ ∈ geodesicChartDomain (I := I) α := hp₀
  have hsmooth_on := geodesicVectorFieldChart_contMDiffOn (I := I) g α
  exact (hsmooth_on p₀ hmem).contMDiffAt (hop.mem_nhds hmem)

end ChartFixedSmoothness

end Geodesic
end Riemannian

end
