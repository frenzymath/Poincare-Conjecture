import PoincareLib.Ch02.CovDerivAlongCurve
import PoincareLib.Ch02.LaplacianCoord
import PoincareLib.Ch02.LaplacianExtremum
import PoincareLib.Ch02.Bochner

/-!
# Morgan–Tian Ch. 2 — the frame bridge: chart covariant derivative is Levi-Civita

Blueprint `lem:cov-deriv-along-curve` (composed-field clause) /
`lem:parallel-gradient-flow`(2): the chart-coordinate covariant derivative
`∂_v Ẑ + Γ(v, Z(x))` produced by `hasCovDerivAlongAt_comp` **is** the abstract
Levi-Civita covariant derivative `(∇_X Z)(x)` whenever `X(x) = v` — the
**frame bridge**. Concretely, at the centre `x` of its own chart,

`(∇_X Z)(x) = D(Ẑ)(φ(x))·X(x) + Γ_g(X(x), Z(x))(φ(x))`,

where `φ = extChartAt I x`, `Ẑ = fieldChartRep x Z` is the chart representation
of `Z`, and `Γ_g` is the chart Christoffel contraction of the metric.

Route (mirrors `hessianAt_chartBasisVecFiber`): expand `Z` (and `X`) near `x`
in the germ-local chart frame of
`exists_chartFrame_nhds_leviCivita_christoffel`, with globally smooth
coefficient functions obtained from the trivialization coordinates via a bump
function (`exists_contMDiff_eventuallyEq_of_contMDiffOn`); then germ locality
of `∇` in the field slot (`cov_congr_apply_right`), pointwise locality in the
direction slot (`cov_congr_apply_left`), the Leibniz rule, and the frame
Christoffel identity reduce everything to chart data at `x`.

Consequences provided here, feeding the splitting cluster:

* `hasCovDerivAlongAt_comp_cov` — `D(Z∘γ)/dt (t₀) = (∇_X Z)(γ t₀)` for any
  global field `X` whose value at `γ t₀` is the velocity of `γ`;
* `hasCovDerivAlongAt_comp_zero` / `isParallelAlong_comp_of_cov_eq_zero` —
  a field with vanishing covariant derivative restricts to a **parallel**
  field along every (chart-regular) curve, the step
  `D(V∘γ)/dt = ∇_{γ'}V = 0` of blueprint `lem:parallel-gradient-flow`(2).

The file also provides the finite-sum infrastructure on `SmoothVectorField`
(`AddCommMonoid` instance, `sumField_apply`, `cov_sum_left/right`) that the
frame expansion needs.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 2
(blueprint `lem:parallel-gradient-flow`).
-/

open Set Filter Riemannian Riemannian.Geodesic Riemannian.Tensor
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

/-! ### Finite sums of smooth vector fields -/

/-- **Math.** Smooth vector fields form an additive commutative monoid under
pointwise addition (they in fact form an `ℝ`-module; only the monoid structure
is needed for finite frame expansions `Σ_k f_k X_k`). -/
noncomputable instance : AddCommMonoid (SmoothVectorField I M) where
  add_assoc a b c := SmoothVectorField.ext fun p => add_assoc (a p) (b p) (c p)
  zero_add a := SmoothVectorField.ext fun p => zero_add (a p)
  add_zero a := SmoothVectorField.ext fun p => add_zero (a p)
  add_comm a b := SmoothVectorField.ext fun p => add_comm (a p) (b p)
  nsmul := nsmulRec

/-- **Math.** A finite sum of smooth vector fields evaluates pointwise. -/
@[simp] theorem sumField_apply {ι : Type*} (s : Finset ι)
    (W : ι → SmoothVectorField I M) (p : M) :
    (∑ i ∈ s, W i) p = ∑ i ∈ s, W i p := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, SmoothVectorField.add_apply, ih]

/-- **Math.** `∇` is additive over finite sums in the field slot. -/
theorem cov_sum_right {ι : Type*} (nabla : AffineConnection I M)
    (X : SmoothVectorField I M) (s : Finset ι)
    (W : ι → SmoothVectorField I M) (p : M) :
    (nabla.cov X (∑ i ∈ s, W i)) p = ∑ i ∈ s, (nabla.cov X (W i)) p := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using nabla.cov_zero_right X p
  | cons a t ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, ← ih]
      have h := congrArg (fun F : SmoothVectorField I M => F p)
        (nabla.add_right X (W a) (∑ i ∈ t, W i))
      simpa using h

/-- **Math.** `∇` is additive over finite sums in the direction slot. -/
theorem cov_sum_left {ι : Type*} (nabla : AffineConnection I M)
    (s : Finset ι) (W : ι → SmoothVectorField I M)
    (Z : SmoothVectorField I M) (p : M) :
    (nabla.cov (∑ i ∈ s, W i) Z) p = ∑ i ∈ s, (nabla.cov (W i) Z) p := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using nabla.cov_zero_left Z p
  | cons a t ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, ← ih]
      have h := congrArg (fun F : SmoothVectorField I M => F p)
        (nabla.add_left (W a) (∑ i ∈ t, W i) Z)
      simpa using h

/-- **Math.** `𝒟(M)`-homogeneity of `∇` in the direction slot, pointwise:
`(∇_{fX} Z)(p) = f(p)·(∇_X Z)(p)`. -/
theorem cov_smul_left_apply (nabla : AffineConnection I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (X Z : SmoothVectorField I M) (p : M) :
    (nabla.cov (SmoothVectorField.smul f hf X) Z) p = f p • (nabla.cov X Z) p := by
  have h := congrArg (fun F : SmoothVectorField I M => F p)
    (nabla.smul_left f hf X Z)
  simpa using h

/-! ### Smoothness of the chart coordinates of a field -/

/-- **Math.** The chart-`x` coordinate representation of a smooth vector field
is smooth on the trivialization base set (= the chart source): a smooth
section read through a trivialization is smooth over its base set. -/
theorem contMDiffOn_fieldRep (x : M) (Z : SmoothVectorField I M) :
    ContMDiffOn I 𝓘(ℝ, E) ∞ (fieldRep (I := I) x Z)
      (trivializationAt E (TangentSpace I) x).baseSet :=
  (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
    (trivializationAt E (TangentSpace I) x)).mp Z.smooth.contMDiffOn

/-- **Math.** Each chart coordinate `Z^k = ⟨φ(Z), e^k⟩` of a smooth vector
field is a smooth scalar function on the chart source. -/
theorem contMDiffOn_chartCoord_fieldRep (x : M) (Z : SmoothVectorField I M)
    (k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun q => Geodesic.chartCoord (E := E) k (fieldRep (I := I) x Z q))
      (trivializationAt E (TangentSpace I) x).baseSet := by
  have hL : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (Geodesic.chartCoordFunctional (E := E) k) :=
    (Geodesic.chartCoordFunctional (E := E) k).contMDiff
  have h := hL.comp_contMDiffOn (contMDiffOn_fieldRep (I := I) x Z)
  refine h.congr fun q _ => ?_
  simp [Function.comp]

/-- **Math.** The chart coordinates of a smooth vector field near `x` are
germs of globally smooth scalar functions: bump-function extension of the
trivialization coordinates. -/
theorem exists_contMDiff_coeff [T2Space M] (x : M) (Z : SmoothVectorField I M) :
    ∃ f : Fin (Module.finrank ℝ E) → M → ℝ,
      (∀ k, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f k)) ∧
        ∀ k, ∀ᶠ q in 𝓝 x, f k q
          = Geodesic.chartCoord (E := E) k (fieldRep (I := I) x Z q) := by
  classical
  have hopen : IsOpen (trivializationAt E (TangentSpace I) x).baseSet :=
    (trivializationAt E (TangentSpace I) x).open_baseSet
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  choose f hf hev using fun k =>
    exists_contMDiff_eventuallyEq_of_contMDiffOn hopen hx
      (contMDiffOn_chartCoord_fieldRep (I := I) x Z k)
  exact ⟨f, hf, hev⟩

/-- **Math.** A smooth vector field agrees near `x` with its chart-frame
expansion `Σ_k Z^k X_k`, for any coefficient functions agreeing near `x` with
the chart coordinates of `Z` and any frame fields agreeing near `x` with the
chart frame. -/
theorem eventually_eq_sum_coeff_smul_frame (x : M) (Z : SmoothVectorField I M)
    {f : Fin (Module.finrank ℝ E) → M → ℝ}
    (hev : ∀ k, ∀ᶠ q in 𝓝 x, f k q
      = Geodesic.chartCoord (E := E) k (fieldRep (I := I) x Z q))
    {Xf : Fin (Module.finrank ℝ E) → SmoothVectorField I M}
    (hXf : ∀ a, ∀ᶠ q in 𝓝 x, Xf a q = chartBasisVecFiber (I := I) x a q) :
    ∀ᶠ q in 𝓝 x, Z q = ∑ k, f k q • Xf k q := by
  have hopen : IsOpen (trivializationAt E (TangentSpace I) x).baseSet :=
    (trivializationAt E (TangentSpace I) x).open_baseSet
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  filter_upwards [eventually_all.mpr hev, eventually_all.mpr hXf,
    hopen.mem_nhds hx] with q hq hqXf hqb
  have hqs : q ∈ (chartAt H x).source := by
    rwa [trivializationAt_baseSet_eq_chartAt_source] at hqb
  calc Z q
      = ∑ k, Geodesic.chartCoord (E := E) k
          (chartFiberCoord (I := I) x ⟨q, Z q⟩)
            • chartBasisVecFiber (I := I) x k q :=
        (sum_chartCoord_smul_chartBasisVecFiber (I := I) x hqs (Z q)).symm
    _ = ∑ k, f k q • Xf k q := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hq k, hqXf k]
        rfl
/-! ### The frame bridge -/

/-- **Math.** Read a tangent vector at `b` as a model-space vector. The two
types are definitionally equal, but their algebraic instance terms differ
syntactically; wrapping values in `toModel` forces subsequent `•`/`∑`
elaboration to happen with the `E`-instances, which is what the model-space
lemmas (`map_smul`, `Finset.smul_sum`, basis coordinates) match against. -/
def toModel {b : M} (v : TangentSpace I b) : E := v

/-- **Math.** `toModel` commutes with finite sums (definitionally). -/
theorem toModel_sum {b : M} {ι : Type*} (s : Finset ι)
    (v : ι → TangentSpace I b) :
    toModel (I := I) (∑ i ∈ s, v i) = ∑ i ∈ s, toModel (I := I) (v i) := rfl

/-- **Math.** **The frame bridge** — the chart formula for the Levi-Civita
covariant derivative: at the centre `x` of its own chart, for smooth vector
fields `X, Z`,

`(∇_X Z)(x) = D(Ẑ)(φ(x))·X(x) + Γ_g(X(x), Z(x))(φ(x))`,

where `φ = extChartAt I x`, `Ẑ = fieldChartRep x Z` is the chart
representation of `Z`, and `Γ_g` is the chart Christoffel contraction of `g`.
This identifies the chart covariant derivative produced by
`hasCovDerivAlongAt_comp` with the abstract Levi-Civita `(∇_X Z)(x)`; in
particular the right-hand side depends on `X` only through `X(x)`.
Blueprint: `lem:parallel-gradient-flow`(2). -/
theorem cov_apply_eq_fderiv_add_chartChristoffelContraction
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    (X Z : SmoothVectorField I M) (x : M) :
    Eq (α := E) ((g.leviCivitaConnection.cov X Z) x)
      (fderiv ℝ (fieldChartRep (I := I) x Z) (extChartAt I x x) (X x)
        + chartChristoffelContraction (I := I) g x (X x) (Z x)
            (extChartAt I x x)) := by
  classical
  have hx : x ∈ (chartAt H x).source := mem_chart_source H x
  -- the germ-local chart frame with its Levi-Civita Christoffel data
  obtain ⟨Xf, hXf, hXfcov⟩ :=
    exists_chartFrame_nhds_leviCivita_christoffel (I := I) g hx
  have hXfvalE : ∀ a, toModel (I := I) (Xf a x) = Module.finBasis ℝ E a := by
    intro a
    show (Xf a x : E) = Module.finBasis ℝ E a
    rw [(hXf a).self_of_nhds]
    exact chartBasisVecFiber_self (I := I) x a
  -- globally smooth chart coefficients of `Z` and `X` near `x`
  obtain ⟨fZ, hfZ, hfZev⟩ := exists_contMDiff_coeff (I := I) x Z
  obtain ⟨fX, hfX, hfXev⟩ := exists_contMDiff_coeff (I := I) x X
  have hfZx : ∀ k, fZ k x = Geodesic.chartCoord (E := E) k (Z x) := by
    intro k
    rw [(hfZev k).self_of_nhds]
    congr 1
    exact chartFiberCoord_mk (I := I) x (Z x)
  have hfXx : ∀ i, fX i x = Geodesic.chartCoord (E := E) i (X x) := by
    intro i
    rw [(hfXev i).self_of_nhds]
    congr 1
    exact chartFiberCoord_mk (I := I) x (X x)
  -- the frame expansions as global smooth fields
  set Z' : SmoothVectorField I M
    := ∑ k, SmoothVectorField.smul (fZ k) (hfZ k) (Xf k) with hZ'def
  set X' : SmoothVectorField I M
    := ∑ i, SmoothVectorField.smul (fX i) (hfX i) (Xf i) with hX'def
  -- `∇` only sees the germ of the field slot at `x`
  have hcovZZ' : (g.leviCivitaConnection.cov X Z) x
      = (g.leviCivitaConnection.cov X Z') x := by
    refine cov_congr_apply_right (I := I) g.leviCivitaConnection X ?_
    filter_upwards [eventually_eq_sum_coeff_smul_frame (I := I) x Z hfZev hXf]
      with q hq
    rw [hq, hZ'def, sumField_apply]
    rfl
  -- `∇` only sees the value of the direction slot at `x`
  have hXX' : X x = X' x := by
    have h := (eventually_eq_sum_coeff_smul_frame (I := I) x X
      hfXev hXf).self_of_nhds
    rw [h, hX'def, sumField_apply]
    rfl
  -- Leibniz expansion of `∇_X Z'` at `x`, read in the model space
  have hexpE : toModel (I := I) ((g.leviCivitaConnection.cov X Z') x)
      = ∑ k, (fZ k x • toModel (I := I) ((g.leviCivitaConnection.cov X (Xf k)) x)
          + X.dir (fZ k) x • toModel (I := I) (Xf k x)) := by
    have h1 : (g.leviCivitaConnection.cov X Z') x
        = ∑ k, (g.leviCivitaConnection.cov X
            (SmoothVectorField.smul (fZ k) (hfZ k) (Xf k))) x := by
      rw [hZ'def]
      exact cov_sum_right (I := I) g.leviCivitaConnection X Finset.univ _ x
    rw [h1, toModel_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact g.leviCivitaConnection.leibniz (fZ k) (hfZ k) X (Xf k) x
  -- the direction slot reduces to the frame directions
  have hcovXfE : ∀ k,
      toModel (I := I) ((g.leviCivitaConnection.cov X (Xf k)) x)
      = ∑ i, Geodesic.chartCoord (E := E) i (X x)
          • toModel (I := I) ((g.leviCivitaConnection.cov (Xf i) (Xf k)) x) := by
    intro k
    have h1 : (g.leviCivitaConnection.cov X (Xf k)) x
        = (g.leviCivitaConnection.cov X' (Xf k)) x :=
      g.leviCivitaConnection.cov_congr_apply_left (Xf k) hXX'
    have h2 : (g.leviCivitaConnection.cov X' (Xf k)) x
        = ∑ i, (g.leviCivitaConnection.cov
            (SmoothVectorField.smul (fX i) (hfX i) (Xf i)) (Xf k)) x := by
      rw [hX'def]
      exact cov_sum_left (I := I) g.leviCivitaConnection Finset.univ _ (Xf k) x
    rw [h1, h2, toModel_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h3 := cov_smul_left_apply (I := I) g.leviCivitaConnection
      (hfX i) (Xf i) (Xf k) x
    rw [hfXx i] at h3
    exact h3
  -- the Christoffel identity of the frame, read in the model space
  have hXfcovE : ∀ i k,
      toModel (I := I) ((g.leviCivitaConnection.cov (Xf i) (Xf k)) x)
      = ∑ m, chartChristoffel (I := I) g x i k m (extChartAt I x x)
          • Module.finBasis ℝ E m := by
    intro i k
    rw [hXfcov i k, toModel_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact congrArg (fun w : E => chartChristoffel (I := I) g x i k m
      (extChartAt I x x) • w) (hXfvalE m)
  -- the derivative of each coefficient of `Z` along `X` is the chart
  -- directional derivative of the chart representation
  have hdirZ : ∀ k, X.dir (fZ k) x
      = ∑ i, Geodesic.chartCoord (E := E) i (X x)
          * partialDeriv (E := E) i
              (fun y => Geodesic.chartCoord (E := E) k
                (fieldChartRep (I := I) x Z y)) (extChartAt I x x) := by
    intro k
    have hXdecomp : (X x : TangentSpace I x)
        = ∑ i, Geodesic.chartCoord (E := E) i (X x)
            • chartBasisVecFiber (I := I) x i x := by
      have h := sum_chartCoord_smul_chartBasisVecFiber (I := I) x hx (X x)
      rw [chartFiberCoord_mk (I := I) x (X x)] at h
      exact h.symm
    have hstep : ∀ i, mfderiv I 𝓘(ℝ, ℝ) (fZ k) x
        (chartBasisVecFiber (I := I) x i x)
        = partialDeriv (E := E) i
            (fun y => Geodesic.chartCoord (E := E) k
              (fieldChartRep (I := I) x Z y)) (extChartAt I x x) := by
      intro i
      rw [mfderiv_apply_chartBasisVecFiber ((hfZ k).contMDiffAt) x hx i]
      refine partialDeriv_congr_of_eventuallyEq ?_ i
      have htend : Tendsto (extChartAt I x).symm (𝓝 (extChartAt I x x)) (𝓝 x) := by
        have hxx : (extChartAt I x).symm (extChartAt I x x) = x :=
          (extChartAt I x).left_inv (mem_extChartAt_source x)
        have hcont := (continuousAt_extChartAt_symm (I := I) x).tendsto
        rwa [hxx] at hcont
      have hEq : fZ k =ᶠ[𝓝 x]
          fun q => Geodesic.chartCoord (E := E) k (fieldRep (I := I) x Z q) :=
        hfZev k
      refine (hEq.comp_tendsto htend).trans
        (Eventually.of_forall fun y => ?_)
      rfl
    show mfderiv I 𝓘(ℝ, ℝ) (fZ k) x (X x) = _
    conv_lhs => rw [hXdecomp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hstep i]
    rfl
  -- the chart derivative of `Ẑ`, expanded in the model basis
  have hfderivE : fderiv ℝ (fieldChartRep (I := I) x Z) (extChartAt I x x) (X x)
      = ∑ k, (∑ i, Geodesic.chartCoord (E := E) i (X x)
          * partialDeriv (E := E) i
              (fun y => Geodesic.chartCoord (E := E) k
                (fieldChartRep (I := I) x Z y)) (extChartAt I x x))
          • Module.finBasis ℝ E k := by
    have hdiff : DifferentiableAt ℝ (fieldChartRep (I := I) x Z)
        (extChartAt I x x) :=
      (contDiffAt_fieldChartRep (I := I) x Z).differentiableAt (by simp)
    have hcomp : ∀ k, fderiv ℝ (fun y => Geodesic.chartCoordFunctional (E := E) k
        (fieldChartRep (I := I) x Z y)) (extChartAt I x x)
        = (Geodesic.chartCoordFunctional (E := E) k).comp
            (fderiv ℝ (fieldChartRep (I := I) x Z) (extChartAt I x x)) := fun k =>
      ((Geodesic.chartCoordFunctional (E := E) k).hasFDerivAt.comp
        (extChartAt I x x) hdiff.hasFDerivAt).fderiv
    conv_lhs => rw [← (Module.finBasis ℝ E).sum_repr
      (fderiv ℝ (fieldChartRep (I := I) x Z) (extChartAt I x x) (X x))]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    have happ := congrArg (fun L : E →L[ℝ] ℝ => L (X x)) (hcomp k)
    simp only [ContinuousLinearMap.comp_apply] at happ
    have h1 : (Module.finBasis ℝ E).repr
        (fderiv ℝ (fieldChartRep (I := I) x Z) (extChartAt I x x) (X x)) k
        = Geodesic.chartCoordFunctional (E := E) k
            (fderiv ℝ (fieldChartRep (I := I) x Z) (extChartAt I x x) (X x)) := by
      rw [Geodesic.chartCoordFunctional_apply]
      rfl
    rw [h1, ← happ, fderiv_apply_eq_sum_partialDeriv]
    simp only [Geodesic.chartCoordFunctional_apply]
  -- first term: the coefficient derivatives assemble to the chart derivative
  have hterm1 : ∑ k, X.dir (fZ k) x • toModel (I := I) (Xf k x)
      = fderiv ℝ (fieldChartRep (I := I) x Z) (extChartAt I x x) (X x) := by
    rw [hfderivE]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact congrArg₂ (· • ·) (hdirZ k) (hXfvalE k)
  -- second term: the Christoffel contributions assemble to the contraction
  have hterm2 :
      ∑ k, fZ k x • toModel (I := I) ((g.leviCivitaConnection.cov X (Xf k)) x)
      = chartChristoffelContraction (I := I) g x (X x) (Z x)
          (extChartAt I x x) := by
    simp only [hcovXfE, hXfcovE, chartChristoffelContraction_def]
    -- compare coordinates in the model basis
    refine Module.Basis.ext_elem (b := Module.finBasis ℝ E) fun j => ?_
    simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hfZx]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  -- assembly
  have hstep1 : toModel (I := I) ((g.leviCivitaConnection.cov X Z) x)
      = ∑ k, (fZ k x • toModel (I := I) ((g.leviCivitaConnection.cov X (Xf k)) x)
          + X.dir (fZ k) x • toModel (I := I) (Xf k x)) :=
    (congrArg (toModel (I := I)) hcovZZ').trans hexpE
  have hstep2 :
      ∑ k, (fZ k x • toModel (I := I) ((g.leviCivitaConnection.cov X (Xf k)) x)
          + X.dir (fZ k) x • toModel (I := I) (Xf k x))
      = (∑ k, fZ k x
            • toModel (I := I) ((g.leviCivitaConnection.cov X (Xf k)) x))
          + ∑ k, X.dir (fZ k) x • toModel (I := I) (Xf k x) :=
    Finset.sum_add_distrib
  have hfinal := hstep1.trans (hstep2.trans
    ((congrArg₂ (· + ·) hterm2 hterm1).trans (add_comm _ _)))
  exact hfinal

/-! ### Covariant derivative of a composed field along a curve -/

/-- **Math.** Blueprint `lem:cov-deriv-along-curve`, composed-field clause in
its intrinsic form: for a smooth vector field `Z` restricted along a curve `γ`
with chart velocity `v` at `t₀`, and any global smooth field `X` with
`X(γ t₀) = v`,

`D(Z∘γ)/dt (t₀) = (∇_X Z)(γ t₀)`,

the Levi-Civita covariant derivative of `Z` in the direction of the velocity.
This is `hasCovDerivAlongAt_comp` composed with the frame bridge.
Blueprint: `lem:parallel-gradient-flow`(2). -/
theorem hasCovDerivAlongAt_comp_cov [SigmaCompactSpace M] [T2Space M]
    (g : RiemannianMetric I M) {γ : ℝ → M} {t₀ : ℝ}
    (X Z : SmoothVectorField I M)
    (hmem : ∀ᶠ s in 𝓝 t₀, γ s ∈ (chartAt H (γ t₀)).source)
    {v : E} (hv : HasDerivAt (chartLocalCurve (I := I) γ t₀) v t₀)
    (hXv : (X (γ t₀) : E) = v) :
    HasCovDerivAlongAt (I := I) g γ (fun t => Z (γ t)) t₀
      ((g.leviCivitaConnection.cov X Z) (γ t₀)) := by
  have hcomp := hasCovDerivAlongAt_comp (I := I) (g := g) Z hmem hv
  have hbridge := cov_apply_eq_fderiv_add_chartChristoffelContraction
    (I := I) g X Z (γ t₀)
  rw [hXv] at hbridge
  rw [hbridge]
  exact hcomp

/-- **Math.** A smooth vector field with everywhere-vanishing covariant
derivative at `γ t₀` restricts to a field along `γ` with vanishing covariant
derivative at `t₀`: pick a global field `X` through the chart velocity of `γ`
at `t₀` and apply the composed-field formula `D(Z∘γ)/dt = ∇_X Z = 0`.
Blueprint: `lem:parallel-gradient-flow`(2). -/
theorem hasCovDerivAlongAt_comp_zero [SigmaCompactSpace M] [T2Space M]
    (g : RiemannianMetric I M) {γ : ℝ → M} {t₀ : ℝ} (Z : SmoothVectorField I M)
    (hcov : ∀ X : SmoothVectorField I M,
      (g.leviCivitaConnection.cov X Z) (γ t₀) = 0)
    (hmem : ∀ᶠ s in 𝓝 t₀, γ s ∈ (chartAt H (γ t₀)).source)
    {v : E} (hv : HasDerivAt (chartLocalCurve (I := I) γ t₀) v t₀) :
    HasCovDerivAlongAt (I := I) g γ (fun t => Z (γ t)) t₀ 0 := by
  obtain ⟨X, hX⟩ := exists_smoothVectorField_eq (I := I) (γ t₀)
    (v : TangentSpace I (γ t₀))
  have h := hasCovDerivAlongAt_comp_cov (I := I) g X Z hmem hv hX
  rw [hcov X] at h
  exact h

/-- **Math.** Blueprint `lem:parallel-gradient-flow`(2), key step: a smooth
vector field `Z` with `∇Z ≡ 0` (vanishing covariant derivative against every
direction field, at every point) restricts to a **parallel** field along every
chart-regular curve: `D(Z∘γ)/dt = ∇_{γ'} Z = 0`. The regularity hypotheses —
`γ` stays in the moving-foot chart near each time and its chart curve is
differentiable — hold automatically for the geodesics produced by the flow.
Combined with `cov_gradientField_apply_eq_zero_of_bochner` this makes the
gradient field of a Busemann-type function parallel along the flow lines. -/
theorem isParallelAlong_comp_of_cov_eq_zero [SigmaCompactSpace M] [T2Space M]
    (g : RiemannianMetric I M) {γ : ℝ → M} (Z : SmoothVectorField I M)
    (hcov : ∀ (X : SmoothVectorField I M) (p : M),
      (g.leviCivitaConnection.cov X Z) p = 0)
    (hmem : ∀ t, ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H (γ t)).source)
    (hvel : ∀ t, ∃ v : E, HasDerivAt (chartLocalCurve (I := I) γ t) v t) :
    IsParallelAlong (I := I) g γ (fun t => Z (γ t)) := by
  intro t
  obtain ⟨v, hv⟩ := hvel t
  exact hasCovDerivAlongAt_comp_zero (I := I) g Z
    (fun X => hcov X (γ t)) (hmem t) hv

/-- **Math.** Blueprint `lem:parallel-gradient-flow`(1)–(2), Bochner form: if
`f` is smooth with `Δf` and `|∇f|²` constant on a manifold with non-negative
Ricci curvature along the gradient, then the gradient field of `f` restricts
to a **parallel** field along every chart-regular curve —
`D((∇f)^*∘γ)/dt = ∇_{γ'}(∇f)^* = 0`. This combines the Bochner vanishing
`cov_gradientField_apply_eq_zero_of_bochner` (through the uniqueness of the
Levi-Civita connection) with the frame bridge. Applied to the flow lines of
the gradient of a Busemann-type function, this is the parallel-transport step
of the splitting theorem. -/
theorem isParallelAlong_gradientField_comp_of_bochner
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    {γ : ℝ → M}
    (hmem : ∀ t, ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H (γ t)).source)
    (hvel : ∀ t, ∃ v : E, HasDerivAt (chartLocalCurve (I := I) γ t) v t) :
    IsParallelAlong (I := I) g γ (fun t => (gradientField g f hf) (γ t)) := by
  have hLC' : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
  have hEqn : nabla = g.leviCivitaConnection :=
    AffineConnection.leviCivita_unique' g nabla g.leviCivitaConnection hLC hLC'
  refine isParallelAlong_comp_of_cov_eq_zero (I := I) g _ ?_ hmem hvel
  intro X p
  rw [← hEqn]
  exact cov_gradientField_apply_eq_zero_of_bochner g hLC hf hgrad hharm hric X p

end PoincareLib
