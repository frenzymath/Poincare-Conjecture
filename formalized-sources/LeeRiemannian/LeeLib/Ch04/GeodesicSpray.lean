/-
Chapter 4, "Connections", §"Geodesics": **Existence and Uniqueness of Geodesics**
(Lee, Theorem 4.27) and existence of **maximal geodesics** (Corollary 4.28), via
the **geodesic spray** on the tangent bundle `TM`.

Lee's geodesic equation in coordinates is the second-order system (4.16)
`ü^k + Γ^k_{ij}(u) u̇^i u̇^j = 0`, which the standard reduction (4.17)/(4.18) turns
into the first-order flow of the vector field `G ∈ 𝔛(TM)`
`G_{(x,v)} = v^k ∂/∂x^k − v^i v^j Γ^k_{ij}(x) ∂/∂v^k`,
the **geodesic spray**.  A curve `γ` is a geodesic iff it is the base projection of
an integral curve of `G`, so existence/uniqueness of geodesics follows from the
fundamental theorem on flows (mathlib's `IsMIntegralCurveAt` existence/uniqueness
for `C¹` vector fields on boundaryless manifolds).

This file builds the spray for an abstract connection `∇` in `TM` (Lee's abstract
setting, `LeeLib.Ch04.Connection`) read through a fixed chart at a basepoint `α`,
using the chart Christoffel contraction `chartGamma` of `LeeLib.Ch04.ParallelTransport`:

* `sprayFiberCoord α p` — the fibre coordinate `v ∈ E` of `p : TM`, read in the
  trivialization at `α`;
* `geodesicSprayFiber cov b α p = (v, −Γ(v, v)(π p))` — the chart-coordinate spray
  `(4.18)` written as a map `TM → E × E`;
* `geodesicVectorFieldChart cov b α : (p : TM) → T_p(TM)` — the spray as a genuine
  section of `T(TM)`, off-chart extended by the zero section;
* `geodesicVectorFieldChart_contMDiffOn`/`_contMDiffAt` — the spray is `C¹` on the
  chart domain (the one connection-specific smoothness obligation reduces to
  `chartConnectionCoeff_contMDiffOn`, since Lee's Christoffel symbols are honest
  smooth functions on `M`);
* `exists_isMIntegralCurveAt_geodesicVectorFieldChart` — Picard–Lindelöf lift on
  `TM` (mathlib `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`);
* `IsSprayGeodesicAt` — Lee's geodesic predicate as "base projection of a local
  integral curve of the spray";
* `exists_sprayGeodesic_initial` (Theorem 4.27, existence) and
  `sprayGeodesic_eventuallyEq` / `isSprayGeodesicAt_eventuallyEq_of_lift_eq`
  (Theorem 4.27, uniqueness on the common domain, via
  `isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless`);
* `exists_maximalSprayGeodesic` (Corollary 4.28) — the unique maximal geodesic with
  prescribed initial point and velocity, as the union of all local geodesics.

The construction is metric-free: it works for any abstract connection whose
Christoffel symbols are `C¹` on the chart domain (`ContMDiffCovariantDerivativeOn
E 1 cov.toFun (chartAt H α).source`), which is exactly the hypothesis the chart
bridge already carries.
-/
import LeeLib.Ch04.ParallelTransport
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

namespace LeeLib.Ch04

open Bundle Module Manifold Set Filter Function
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*} [Fintype ι] {b : Basis ι ℝ E}

/-- **The fibre coordinate** `v ∈ E` of a tangent vector `p : TM`, read in the
trivialization of `TM` at the basepoint `α` (Lee's `v^i` in the chart at `α`). -/
def sprayFiberCoord (α : M) (p : TangentBundle I M) : E :=
  (trivializationAt E (TangentSpace I) α p).2

@[simp] theorem sprayFiberCoord_def (α : M) (p : TangentBundle I M) :
    sprayFiberCoord (I := I) α p = (trivializationAt E (TangentSpace I) α p).2 := rfl

/-- **The geodesic spray in chart coordinates** (Lee, equation (4.18)), written as a
map `TM → E × E`: at a tangent vector `p` with fibre coordinate `v` (in the chart at
`α`) and base point `π p`, the spray is `(v, −Γ(v, v)(π p))`, where `Γ` is the chart
Christoffel contraction of the connection.  The base component `v` is the velocity;
the fibre component `−Γ(v, v)` is Lee's `−v^i v^j Γ^k_{ij}`. -/
def geodesicSprayFiber (cov : Connection I E (TangentSpace I : M → Type _)) (b : Basis ι ℝ E)
    (α : M) (p : TangentBundle I M) : E × E :=
  let v := sprayFiberCoord (I := I) α p
  (v, - chartGamma cov (trivializationAt E (TangentSpace I) α) b v v p.proj)

/-- **The chart domain** of the spray: the set of `p : TM` whose foot `π p` lies in
the chart source at `α`.  Equal to the base set of the trivialization of `T(TM)` at
the zero vector `⟨α, 0⟩`. -/
def geodesicChartDomain (α : M) : Set (TangentBundle I M) :=
  (Bundle.TotalSpace.proj : TangentBundle I M → M) ⁻¹' (chartAt H α).source

theorem geodesicChartDomain_isOpen (α : M) :
    IsOpen (geodesicChartDomain (I := I) (M := M) α) :=
  (chartAt H α).open_source.preimage (FiberBundle.continuous_proj E (TangentSpace I))

/-- **The geodesic spray as a section of `T(TM)`** (Lee's `G ∈ 𝔛(TM)`): the tangent
vector to `TM` at `p` whose reading in the trivialization of `T(TM)` at `⟨α, 0⟩` is
the chart-coordinate spray `geodesicSprayFiber cov b α p`.  Off the chart domain it
degenerates to the zero section. -/
def geodesicVectorFieldChart (cov : Connection I E (TangentSpace I : M → Type _))
    (b : Basis ι ℝ E) (α : M) (p : TangentBundle I M) : TangentSpace I.tangent p :=
  (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).symm p
    (geodesicSprayFiber cov b α p)

section Smoothness

/-- Projection `TM → M` is smooth (mathlib fact, as a `ContMDiffOn`). -/
theorem proj_contMDiffOn (s : Set (TangentBundle I M)) :
    ContMDiffOn I.tangent I 1
      (Bundle.TotalSpace.proj : TangentBundle I M → M) s :=
  (Bundle.contMDiff_proj (TangentSpace I) (n := (1 : WithTop ℕ∞))).contMDiffOn

/-- **The fibre coordinate `sprayFiberCoord α` is smooth on the chart domain**:
equivalent to the second component of the trivialization of `TM` at `α` being
smooth on its base set (via `Trivialization.contMDiffOn_iff` applied to the
identity). -/
theorem sprayFiberCoord_contMDiffOn (α : M) :
    ContMDiffOn I.tangent 𝓘(ℝ, E) 1
      (sprayFiberCoord (I := I) α) (geodesicChartDomain (I := I) α) := by
  classical
  have he : MapsTo (id : TangentBundle I M → TangentBundle I M)
      (geodesicChartDomain (I := I) α)
      (trivializationAt E (TangentSpace I) α).source := by
    intro p hp
    rw [Trivialization.source_eq, TangentBundle.trivializationAt_baseSet]
    exact hp
  have hiff :=
    (trivializationAt E (TangentSpace I) α).contMDiffOn_iff
      (IM := I.tangent) (IB := I) (n := (1 : WithTop ℕ∞))
      (f := id) (s := geodesicChartDomain (I := I) α) he
  have hid : ContMDiffOn I.tangent (I.prod 𝓘(ℝ, E)) 1
      (id : TangentBundle I M → TangentBundle I M)
      (geodesicChartDomain (I := I) α) := contMDiffOn_id
  exact (hiff.mp hid).2

/-- **The chart Christoffel contraction is smooth in `p` on the chart domain**: the
one connection-specific smoothness obligation.  `Γ(v, v)(π p)` with
`v = sprayFiberCoord α p` is a finite sum of products of the `C¹` chart Christoffel
symbols `Γ^k_{ij}(π p)` (smooth by `chartConnectionCoeff_contMDiffOn`, composed with
the smooth projection) and the `C^∞` coordinate functions `b.repr v i` (linear in
the smooth fibre coordinate). -/
theorem chartGamma_sprayFiber_contMDiffOn
    (cov : Connection I E (TangentSpace I : M → Type _)) (α : M)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun
      (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffOn I.tangent 𝓘(ℝ, E) 1
      (fun p : TangentBundle I M =>
        chartGamma cov (trivializationAt E (TangentSpace I) α) b
          (sprayFiberCoord (I := I) α p) (sprayFiberCoord (I := I) α p) p.proj)
      (geodesicChartDomain (I := I) α) := by
  classical
  set e := trivializationAt E (TangentSpace I) α with he
  have hproj : ContMDiffOn I.tangent I 1
      (Bundle.TotalSpace.proj : TangentBundle I M → M) (geodesicChartDomain (I := I) α) :=
    proj_contMDiffOn _
  have hmaps : MapsTo (Bundle.TotalSpace.proj : TangentBundle I M → M)
      (geodesicChartDomain (I := I) α) e.baseSet := by
    intro p hp; rw [he, TangentBundle.trivializationAt_baseSet]; exact hp
  have hv : ContMDiffOn I.tangent 𝓘(ℝ, E) 1
      (sprayFiberCoord (I := I) α) (geodesicChartDomain (I := I) α) :=
    sprayFiberCoord_contMDiffOn α
  -- Smoothness of one coordinate function `p ↦ b.repr (sprayFiberCoord α p) i`.
  have hrepr : ∀ i : ι, ContMDiffOn I.tangent 𝓘(ℝ) 1
      (fun p : TangentBundle I M => b.repr (sprayFiberCoord (I := I) α p) i)
      (geodesicChartDomain (I := I) α) := by
    intro i
    have hcoe : (fun p : TangentBundle I M => b.repr (sprayFiberCoord (I := I) α p) i)
        = fun p => (b.coord i).toContinuousLinearMap (sprayFiberCoord (I := I) α p) := by
      funext p; rw [LinearMap.coe_toContinuousLinearMap', Basis.coord_apply]
    rw [hcoe]
    exact ((b.coord i).toContinuousLinearMap.contMDiff).comp_contMDiffOn hv
  simp only [chartGamma_def]
  refine contMDiffOn_finsetSum fun k _ => ?_
  have hconst : ContMDiffOn I.tangent 𝓘(ℝ, E) 1
      (fun _ : TangentBundle I M => b k) (geodesicChartDomain (I := I) α) := contMDiffOn_const
  have hscalar : ContMDiffOn I.tangent 𝓘(ℝ) 1
      (fun p : TangentBundle I M =>
        ∑ i, ∑ j, chartConnectionCoeff cov e b i j k p.proj
          * b.repr (sprayFiberCoord (I := I) α p) i * b.repr (sprayFiberCoord (I := I) α p) j)
      (geodesicChartDomain (I := I) α) := by
    refine contMDiffOn_finsetSum fun i _ => contMDiffOn_finsetSum fun j _ => ?_
    have hΓ : ContMDiffOn I.tangent 𝓘(ℝ) 1
        (fun p : TangentBundle I M => chartConnectionCoeff cov e b i j k p.proj)
        (geodesicChartDomain (I := I) α) :=
      (chartConnectionCoeff_contMDiffOn cov hcov i j k).comp hproj hmaps
    exact (hΓ.mul (hrepr i)).mul (hrepr j)
  exact hscalar.smul hconst

/-- **The chart-coordinate spray `geodesicSprayFiber cov b α` is smooth** as a map
`TM → E × E` on the chart domain (both components are smooth). -/
theorem geodesicSprayFiber_contMDiffOn
    (cov : Connection I E (TangentSpace I : M → Type _)) (α : M)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun
      (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffOn I.tangent 𝓘(ℝ, E × E) 1
      (geodesicSprayFiber cov b α) (geodesicChartDomain (I := I) α) := by
  have hfst : ContMDiffOn I.tangent 𝓘(ℝ, E) 1
      (sprayFiberCoord (I := I) α) (geodesicChartDomain (I := I) α) :=
    sprayFiberCoord_contMDiffOn α
  have hsnd : ContMDiffOn I.tangent 𝓘(ℝ, E) 1
      (fun p : TangentBundle I M =>
        - chartGamma cov (trivializationAt E (TangentSpace I) α) b
          (sprayFiberCoord (I := I) α p) (sprayFiberCoord (I := I) α p) p.proj)
      (geodesicChartDomain (I := I) α) :=
    (chartGamma_sprayFiber_contMDiffOn cov α hcov).neg
  exact hfst.prodMk_space hsnd

/-- The chart domain coincides with the base set of the trivialization of `T(TM)` at
`⟨α, 0⟩`. -/
theorem geodesicChartDomain_eq_trivBaseSet (α : M) :
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

/-- The trivialization of `T(TM)` at `⟨α, 0⟩` is in the canonical atlas. -/
private instance trivializationAt_tangent_tangent_isAtlas (α : M) :
    MemTrivializationAtlas
      (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)) :=
  ⟨FiberBundle.trivialization_mem_atlas (E × E) (TangentSpace I.tangent) _⟩

/-- By construction, applying the trivialization of `T(TM)` at `⟨α, 0⟩` to the spray
section returns the chart-coordinate spray on the chart domain. -/
theorem trivializationAt_apply_geodesicVectorFieldChart
    (cov : Connection I E (TangentSpace I : M → Type _)) (b : Basis ι ℝ E) (α : M)
    {p : TangentBundle I M} (hp : p ∈ geodesicChartDomain (I := I) α) :
    (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M))
      ⟨p, geodesicVectorFieldChart cov b α p⟩ =
        (p, geodesicSprayFiber cov b α p) := by
  classical
  have hp' : p ∈ (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).baseSet := by
    rw [← geodesicChartDomain_eq_trivBaseSet (I := I) α]; exact hp
  exact (trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M)).apply_mk_symm hp'
      (geodesicSprayFiber cov b α p)

/-- **The geodesic spray section is `C¹` on the chart domain.**  Via
`Trivialization.contMDiffOn_iff` for `T(TM)` at `⟨α, 0⟩`: the base part is the
identity (smooth) and the fibre part is the chart-coordinate spray
(`geodesicSprayFiber_contMDiffOn`). -/
theorem geodesicVectorFieldChart_contMDiffOn
    (cov : Connection I E (TangentSpace I : M → Type _)) (α : M)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun
      (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffOn I.tangent I.tangent.tangent 1
      (fun p : TangentBundle I M =>
        (⟨p, geodesicVectorFieldChart cov b α p⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      (geodesicChartDomain (I := I) α) := by
  classical
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M) with he
  have hMapsTo : MapsTo
      (fun p : TangentBundle I M =>
        (⟨p, geodesicVectorFieldChart cov b α p⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      (geodesicChartDomain (I := I) α) e.source := by
    intro p hp
    rw [Trivialization.source_eq]
    rw [← geodesicChartDomain_eq_trivBaseSet (I := I) α]
    exact hp
  rw [e.contMDiffOn_iff (IM := I.tangent) (IB := I.tangent)
    (n := (1 : WithTop ℕ∞)) hMapsTo]
  refine ⟨?_, ?_⟩
  · have hid : (fun p : TangentBundle I M =>
        (⟨p, geodesicVectorFieldChart cov b α p⟩ :
          TangentBundle I.tangent (TangentBundle I M)).proj) =
        (fun p : TangentBundle I M => p) := rfl
    rw [hid]
    exact contMDiffOn_id
  · have heq : ∀ p ∈ geodesicChartDomain (I := I) α,
        (e ⟨p, geodesicVectorFieldChart cov b α p⟩).2 =
          geodesicSprayFiber cov b α p := by
      intro p hp
      rw [he, trivializationAt_apply_geodesicVectorFieldChart cov b α hp]
    have hsmooth : ContMDiffOn I.tangent 𝓘(ℝ, E × E) 1
        (geodesicSprayFiber cov b α) (geodesicChartDomain (I := I) α) :=
      geodesicSprayFiber_contMDiffOn cov α hcov
    exact hsmooth.congr heq

/-- **`ContMDiffAt` form** of the spray smoothness, suitable for mathlib's
integral-curve existence/uniqueness theorems: at every `p₀` whose foot lies in the
chart source at `α`, the geodesic spray section is `C¹`. -/
theorem geodesicVectorFieldChart_contMDiffAt
    (cov : Connection I E (TangentSpace I : M → Type _)) (α : M)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun
      (trivializationAt E (TangentSpace I) α).baseSet)
    {p₀ : TangentBundle I M} (hp₀ : p₀.proj ∈ (chartAt H α).source) :
    ContMDiffAt I.tangent I.tangent.tangent 1
      (fun p : TangentBundle I M =>
        (⟨p, geodesicVectorFieldChart cov b α p⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      p₀ := by
  have hop : IsOpen (geodesicChartDomain (I := I) α) :=
    geodesicChartDomain_isOpen (I := I) (M := M) α
  have hmem : p₀ ∈ geodesicChartDomain (I := I) α := hp₀
  exact ((geodesicVectorFieldChart_contMDiffOn cov α hcov) p₀ hmem).contMDiffAt
    (hop.mem_nhds hmem)

end Smoothness

section ExistenceUniqueness

/-- **Picard–Lindelöf lift for the geodesic spray** (Lee, Theorem 4.27, existence
core).  For a `C¹` connection on the chart domain at `α` and a tangent vector `p₀`
whose foot lies in the chart source, there is a curve `f : ℝ → TM` with `f t₀ = p₀`
that is a local integral curve of the geodesic spray.  Directly from mathlib's
`exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless` applied to the `C¹` spray. -/
theorem exists_isMIntegralCurveAt_geodesicVectorFieldChart
    (cov : Connection I E (TangentSpace I : M → Type _)) (α : M)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun
      (trivializationAt E (TangentSpace I) α).baseSet)
    {p₀ : TangentBundle I M} (hp₀ : p₀.proj ∈ (chartAt H α).source) (t₀ : ℝ) :
    ∃ f : ℝ → TangentBundle I M,
      f t₀ = p₀ ∧ IsMIntegralCurveAt f (geodesicVectorFieldChart cov b α) t₀ := by
  have hsmooth1 : ContMDiffAt I.tangent I.tangent.tangent 1
      (fun p : TangentBundle I M =>
        (⟨p, geodesicVectorFieldChart cov b α p⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      p₀ :=
    geodesicVectorFieldChart_contMDiffAt cov α hcov hp₀
  exact exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
    (I := I.tangent) (M := TangentBundle I M)
    (v := geodesicVectorFieldChart cov b α)
    (t₀ := t₀) (x₀ := p₀) hsmooth1

/-- The base projection of a bundle curve `f : ℝ → TM` to `M`. -/
def projectCurve (f : ℝ → TangentBundle I M) : ℝ → M := fun t => (f t).proj

@[simp] theorem projectCurve_apply (f : ℝ → TangentBundle I M) (t : ℝ) :
    projectCurve (I := I) f t = (f t).proj := rfl

/-- **Lee's geodesic predicate**, spray form (Lee, §"Geodesics"): a curve `γ : ℝ → M`
is a geodesic at `t₀` if it is the base projection of a local integral curve `f` of
the geodesic spray (with basepoint chart `α`), whose foot at `t₀` lies in the chart
source.  This is Lee's characterization "a geodesic is a curve whose velocity field is
parallel", packaged through the spray/integral-curve reduction (4.16)–(4.18). -/
def IsSprayGeodesicAt (cov : Connection I E (TangentSpace I : M → Type _))
    (b : Basis ι ℝ E) (γ : ℝ → M) (t₀ : ℝ) : Prop :=
  ∃ (α : M) (f : ℝ → TangentBundle I M),
    (∀ t, (f t).proj = γ t) ∧
    (f t₀).proj ∈ (chartAt H α).source ∧
    IsMIntegralCurveAt f (geodesicVectorFieldChart cov b α) t₀

/-- **Existence of geodesics with prescribed initial data** (Lee, Theorem 4.27,
existence).  For any point `p`, initial velocity `v ∈ T_p M`, and initial time `t₀`,
with the connection `C¹` on the chart at `p`, there is a geodesic `γ` through `p`,
carried by a lift `f` with `f t₀ = ⟨p, v⟩` (so the initial point is `p` and the
initial velocity — the fibre coordinate — is `v`).  In particular `IsSprayGeodesicAt`
holds at `t₀`. -/
theorem exists_sprayGeodesic_initial
    (cov : Connection I E (TangentSpace I : M → Type _)) (b : Basis ι ℝ E)
    (p : M) (v : TangentSpace I p) (t₀ : ℝ)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun
      (trivializationAt E (TangentSpace I) p).baseSet) :
    ∃ (γ : ℝ → M) (f : ℝ → TangentBundle I M),
      f t₀ = (⟨p, v⟩ : TangentBundle I M) ∧
      γ = projectCurve (I := I) f ∧
      γ t₀ = p ∧
      IsMIntegralCurveAt f (geodesicVectorFieldChart cov b p) t₀ ∧
      IsSprayGeodesicAt cov b γ t₀ := by
  have hp₀ : (⟨p, v⟩ : TangentBundle I M).proj ∈ (chartAt H p).source :=
    mem_chart_source H p
  obtain ⟨f, hf0, hf⟩ :=
    exists_isMIntegralCurveAt_geodesicVectorFieldChart (b := b) cov p hcov hp₀ t₀
  refine ⟨projectCurve (I := I) f, f, hf0, rfl, ?_, hf, ?_⟩
  · simp [projectCurve, hf0]
  · refine ⟨p, f, fun t => rfl, ?_, hf⟩
    rw [show (f t₀).proj = p by simp [hf0]]
    exact mem_chart_source H p

/-- **Uniqueness of integral curves of the geodesic spray** (the analytic core of
Lee's Theorem 4.27 uniqueness).  Two local integral curves of the geodesic spray at
`t₀` that agree at `t₀` agree near `t₀`, provided the common foot lies in the chart
source (so the spray is smooth there).  Directly from mathlib's
`isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless`. -/
theorem isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
    (cov : Connection I E (TangentSpace I : M → Type _)) {α : M} {t₀ : ℝ}
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun
      (trivializationAt E (TangentSpace I) α).baseSet)
    {f₁ f₂ : ℝ → TangentBundle I M}
    (hα_src : (f₁ t₀).proj ∈ (chartAt H α).source)
    (hf₁ : IsMIntegralCurveAt f₁ (geodesicVectorFieldChart cov b α) t₀)
    (hf₂ : IsMIntegralCurveAt f₂ (geodesicVectorFieldChart cov b α) t₀)
    (h0 : f₁ t₀ = f₂ t₀) :
    f₁ =ᶠ[𝓝 t₀] f₂ := by
  have hsmooth1 : ContMDiffAt I.tangent I.tangent.tangent 1
      (fun p : TangentBundle I M =>
        (⟨p, geodesicVectorFieldChart cov b α p⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      (f₁ t₀) :=
    geodesicVectorFieldChart_contMDiffAt cov α hcov hα_src
  exact isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
    (I := I.tangent) (M := TangentBundle I M)
    (v := geodesicVectorFieldChart cov b α)
    (γ := f₁) (γ' := f₂) (t₀ := t₀) hsmooth1 hf₁ hf₂ h0

/-- **Uniqueness of geodesics with matching initial data** (Lee, Theorem 4.27,
uniqueness: "any two such geodesics agree on their common domain").  Two geodesics
`γ₁, γ₂` carried by lifts of the geodesic spray with the same chart basepoint `α`,
agreeing on the lift at `t₀` (which encodes matching initial point *and* velocity),
agree on a neighbourhood of `t₀`. -/
theorem sprayGeodesic_eventuallyEq
    (cov : Connection I E (TangentSpace I : M → Type _)) {γ₁ γ₂ : ℝ → M} {α : M} {t₀ : ℝ}
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun
      (trivializationAt E (TangentSpace I) α).baseSet)
    {f₁ f₂ : ℝ → TangentBundle I M}
    (hα_src : γ₁ t₀ ∈ (chartAt H α).source)
    (hproj₁ : ∀ t, (f₁ t).proj = γ₁ t) (hproj₂ : ∀ t, (f₂ t).proj = γ₂ t)
    (hf₁ : IsMIntegralCurveAt f₁ (geodesicVectorFieldChart cov b α) t₀)
    (hf₂ : IsMIntegralCurveAt f₂ (geodesicVectorFieldChart cov b α) t₀)
    (h0 : f₁ t₀ = f₂ t₀) :
    γ₁ =ᶠ[𝓝 t₀] γ₂ := by
  have hα_src' : (f₁ t₀).proj ∈ (chartAt H α).source := by rw [hproj₁ t₀]; exact hα_src
  have heq := isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
    (b := b) cov hcov hα_src' hf₁ hf₂ h0
  refine heq.mono fun t ht => ?_
  rw [← hproj₁ t, ← hproj₂ t]; exact congrArg _ ht

/-- **Uniqueness with the initial point as chart basepoint** (Lee, Theorem 4.27,
uniqueness).  Specialising `sprayGeodesic_eventuallyEq` to the chart basepoint
`α := γ₁ t₀` (automatically in its own chart source), two geodesics whose lifts agree
at `t₀` agree on a neighbourhood of `t₀`. -/
theorem isSprayGeodesicAt_eventuallyEq_of_lift_eq
    (cov : Connection I E (TangentSpace I : M → Type _)) {γ₁ γ₂ : ℝ → M} {t₀ : ℝ}
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun
      (trivializationAt E (TangentSpace I) (γ₁ t₀)).baseSet)
    {f₁ f₂ : ℝ → TangentBundle I M}
    (hproj₁ : ∀ t, (f₁ t).proj = γ₁ t) (hproj₂ : ∀ t, (f₂ t).proj = γ₂ t)
    (hf₁ : IsMIntegralCurveAt f₁ (geodesicVectorFieldChart cov b (γ₁ t₀)) t₀)
    (hf₂ : IsMIntegralCurveAt f₂ (geodesicVectorFieldChart cov b (γ₁ t₀)) t₀)
    (h0 : f₁ t₀ = f₂ t₀) :
    γ₁ =ᶠ[𝓝 t₀] γ₂ :=
  sprayGeodesic_eventuallyEq (b := b) cov hcov (mem_chart_source H (γ₁ t₀))
    hproj₁ hproj₂ hf₁ hf₂ h0

end ExistenceUniqueness

section MaximalGeodesic
/-!
### Maximal geodesics (Lee, Corollary 4.28)

The maximal interval of definition of a geodesic with initial data `(p, v)` is the
union of all open intervals containing `0` on which such a geodesic exists; local
uniqueness makes the union a well-defined geodesic (the canonical maximal geodesic).
We build the interval, prove it open and containing `0`, and define the canonical
maximal geodesic curve.  Following the same scope as the reference development, the
globalised "geodesic on the whole maximal interval" statement would require gluing the
chart-fixed integral curves across chart changes (a moving-chart geodesic equation)
and is left to a later development; here the geodesic regularity is recorded pointwise
as `IsSprayGeodesicAt` at each interior point whose foot stays in the base chart.
-/

/-- **Interval-restricted geodesic with initial data** `(p, v)` at time `0`: the
velocity lift `f` projects to `γ`, satisfies `f 0 = ⟨p, v⟩`, and is an integral curve
of the geodesic spray with chart basepoint `p` (so the spray is smooth at the initial
data, `p ∈ (chartAt H p).source` automatically). -/
def IsSprayGeodesicOnWithInitial (cov : Connection I E (TangentSpace I : M → Type _))
    (b : Basis ι ℝ E) (γ : ℝ → M) (s : Set ℝ) (p : M) (v : TangentSpace I p) : Prop :=
  ∃ f : ℝ → TangentBundle I M,
    (∀ t, (f t).proj = γ t) ∧
    f 0 = (⟨p, v⟩ : TangentBundle I M) ∧
    IsMIntegralCurveOn f (geodesicVectorFieldChart cov b p) s

/-- An interval geodesic is, at every interior point of `s` whose foot stays in the
base chart-source, a local spray geodesic `IsSprayGeodesicAt` with basepoint `p`. -/
theorem IsSprayGeodesicOnWithInitial.isSprayGeodesicAt
    {cov : Connection I E (TangentSpace I : M → Type _)} {b : Basis ι ℝ E}
    {γ : ℝ → M} {s : Set ℝ} {p : M} {v : TangentSpace I p} {t : ℝ}
    (hγ : IsSprayGeodesicOnWithInitial cov b γ s p v) (ht : s ∈ 𝓝 t)
    (ht_src : γ t ∈ (chartAt H p).source) :
    IsSprayGeodesicAt cov b γ t := by
  obtain ⟨f, hproj, _, hf⟩ := hγ
  refine ⟨p, f, hproj, ?_, hf.isMIntegralCurveAt ht⟩
  rw [hproj t]; exact ht_src

/-- The starting point is forced: `γ 0 = p`. -/
theorem IsSprayGeodesicOnWithInitial.start_eq
    {cov : Connection I E (TangentSpace I : M → Type _)} {b : Basis ι ℝ E}
    {γ : ℝ → M} {s : Set ℝ} {p : M} {v : TangentSpace I p}
    (hγ : IsSprayGeodesicOnWithInitial cov b γ s p v) :
    γ 0 = p := by
  obtain ⟨f, hproj, hf0, _⟩ := hγ
  have h := hproj 0
  simp [hf0] at h
  exact h.symm

/-- `IsSprayGeodesicOnWithInitial` is monotone in the set. -/
theorem IsSprayGeodesicOnWithInitial.mono
    {cov : Connection I E (TangentSpace I : M → Type _)} {b : Basis ι ℝ E}
    {γ : ℝ → M} {s s' : Set ℝ} {p : M} {v : TangentSpace I p}
    (hγ : IsSprayGeodesicOnWithInitial cov b γ s p v) (hs : s' ⊆ s) :
    IsSprayGeodesicOnWithInitial cov b γ s' p v := by
  obtain ⟨f, hproj, hf0, hf⟩ := hγ
  exact ⟨f, hproj, hf0, hf.mono hs⟩

/-- **Membership witness** for the maximal interval at time `t`: a preconnected open
`J ∋ 0, t` carrying a geodesic with initial data `(p, v)`. -/
def MaximalSprayGeodesicWitness (cov : Connection I E (TangentSpace I : M → Type _))
    (b : Basis ι ℝ E) (p : M) (v : TangentSpace I p) (t : ℝ) : Prop :=
  ∃ γ : ℝ → M, ∃ J : Set ℝ,
    IsOpen J ∧ IsPreconnected J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsSprayGeodesicOnWithInitial cov b γ J p v

/-- **The maximal interval of definition** of a geodesic with initial data `(p, v)`:
the set of times `t` admitting an open interval `J ∋ 0, t` on which such a geodesic is
defined (Lee, Corollary 4.28). -/
def maximalSprayGeodesicInterval (cov : Connection I E (TangentSpace I : M → Type _))
    (b : Basis ι ℝ E) (p : M) (v : TangentSpace I p) : Set ℝ :=
  {t : ℝ | MaximalSprayGeodesicWitness cov b p v t}

theorem mem_maximalSprayGeodesicInterval_iff
    {cov : Connection I E (TangentSpace I : M → Type _)} {b : Basis ι ℝ E}
    {p : M} {v : TangentSpace I p} {t : ℝ} :
    t ∈ maximalSprayGeodesicInterval cov b p v ↔ MaximalSprayGeodesicWitness cov b p v t :=
  Iff.rfl

/-- **The maximal interval is open.** -/
theorem maximalSprayGeodesicInterval_isOpen
    (cov : Connection I E (TangentSpace I : M → Type _)) (b : Basis ι ℝ E)
    (p : M) (v : TangentSpace I p) :
    IsOpen (maximalSprayGeodesicInterval cov b p v) := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  obtain ⟨γ, J, hJ, hJ_conn, h0, ht_in, hγ⟩ := ht
  refine Filter.mem_of_superset (hJ.mem_nhds ht_in) fun t' ht' => ?_
  exact ⟨γ, J, hJ, hJ_conn, h0, ht', hγ⟩

/-- The Picard–Lindelöf local geodesic gives an open interval `J ∋ 0` carrying a
geodesic with initial data `(p, v)`, witnessing `0 ∈` the maximal interval. -/
theorem exists_maximalSprayGeodesicWitness_zero
    (cov : Connection I E (TangentSpace I : M → Type _)) (b : Basis ι ℝ E)
    (p : M) (v : TangentSpace I p)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun
      (trivializationAt E (TangentSpace I) p).baseSet) :
    MaximalSprayGeodesicWitness cov b p v 0 := by
  have hp₀ : (⟨p, v⟩ : TangentBundle I M).proj ∈ (chartAt H p).source := mem_chart_source H p
  obtain ⟨f, hf0, hf⟩ :=
    exists_isMIntegralCurveAt_geodesicVectorFieldChart (b := b) cov p hcov hp₀ 0
  rw [isMIntegralCurveAt_iff'] at hf
  obtain ⟨ε, hε, hf_on⟩ := hf
  refine ⟨projectCurve (I := I) f, Metric.ball (0 : ℝ) ε,
    Metric.isOpen_ball, (convex_ball (0 : ℝ) ε).isPreconnected,
    Metric.mem_ball_self hε, Metric.mem_ball_self hε, ?_⟩
  exact ⟨f, fun _ => rfl, hf0, hf_on⟩

/-- **`0` belongs to the maximal interval** (needs the connection `C¹` on the chart at
`p`). -/
theorem zero_mem_maximalSprayGeodesicInterval
    (cov : Connection I E (TangentSpace I : M → Type _)) (b : Basis ι ℝ E)
    (p : M) (v : TangentSpace I p)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun
      (trivializationAt E (TangentSpace I) p).baseSet) :
    (0 : ℝ) ∈ maximalSprayGeodesicInterval cov b p v :=
  exists_maximalSprayGeodesicWitness_zero cov b p v hcov

/-- **The maximal interval is nonempty.** -/
theorem maximalSprayGeodesicInterval_nonempty
    (cov : Connection I E (TangentSpace I : M → Type _)) (b : Basis ι ℝ E)
    (p : M) (v : TangentSpace I p)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun
      (trivializationAt E (TangentSpace I) p).baseSet) :
    (maximalSprayGeodesicInterval cov b p v).Nonempty :=
  ⟨0, zero_mem_maximalSprayGeodesicInterval cov b p v hcov⟩

open Classical in
/-- **The canonical maximal geodesic** with initial data `(p, v)` (Lee, Corollary
4.28).  On the maximal interval it equals some local geodesic with the prescribed
initial data (chosen by `Classical.choose`); off it, the junk value `p`. -/
noncomputable def maximalSprayGeodesic (cov : Connection I E (TangentSpace I : M → Type _))
    (b : Basis ι ℝ E) (p : M) (v : TangentSpace I p) (t : ℝ) : M :=
  if h : MaximalSprayGeodesicWitness cov b p v t then Classical.choose h t else p

/-- Off the maximal interval, `maximalSprayGeodesic` takes the junk value `p`. -/
theorem maximalSprayGeodesic_of_not_mem
    (cov : Connection I E (TangentSpace I : M → Type _)) (b : Basis ι ℝ E)
    {p : M} {v : TangentSpace I p} {t : ℝ}
    (ht : t ∉ maximalSprayGeodesicInterval cov b p v) :
    maximalSprayGeodesic cov b p v t = p := by
  have ht' : ¬ MaximalSprayGeodesicWitness cov b p v t := ht
  rw [maximalSprayGeodesic]; exact dif_neg ht'

/-- On the maximal interval, `maximalSprayGeodesic` equals the chosen local geodesic. -/
theorem maximalSprayGeodesic_of_mem
    (cov : Connection I E (TangentSpace I : M → Type _)) (b : Basis ι ℝ E)
    {p : M} {v : TangentSpace I p} {t : ℝ}
    (h : t ∈ maximalSprayGeodesicInterval cov b p v) :
    maximalSprayGeodesic cov b p v t = Classical.choose h t := by
  have h' : MaximalSprayGeodesicWitness cov b p v t := h
  rw [maximalSprayGeodesic]; exact dif_pos h'

/-- **The canonical maximal geodesic starts at `p`** (`γ 0 = p`). -/
theorem maximalSprayGeodesic_zero
    (cov : Connection I E (TangentSpace I : M → Type _)) (b : Basis ι ℝ E)
    (p : M) (v : TangentSpace I p)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun
      (trivializationAt E (TangentSpace I) p).baseSet) :
    maximalSprayGeodesic cov b p v 0 = p := by
  have h0 := zero_mem_maximalSprayGeodesicInterval cov b p v hcov
  rw [maximalSprayGeodesic_of_mem cov b h0]
  obtain ⟨_J, _hJ, _hJconn, _h0J, _h0J', hγ⟩ := Classical.choose_spec h0
  exact hγ.start_eq

/-- **Structural properties of the canonical maximal geodesic** (Lee, Corollary 4.28,
partial).  With `I_max := maximalSprayGeodesicInterval cov b p v` and
`γ_max := maximalSprayGeodesic cov b p v`: `I_max` is open and contains `0`,
`γ_max 0 = p`, `γ_max = p` off `I_max`, and at every `t ∈ I_max` (whose witnesses keep
their foot in the base chart) there is a local geodesic through `p` that is a spray
geodesic at both `0` and `t`.  The `hsrc` clause is the chart-validity condition where
a witness has not yet left the base chart; the fully globalised geodesic-on-`I_max`
statement is the deferred moving-chart argument. -/
theorem maximalSprayGeodesic_structure_of_footInSource
    (cov : Connection I E (TangentSpace I : M → Type _)) (b : Basis ι ℝ E)
    (p : M) (v : TangentSpace I p)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun
      (trivializationAt E (TangentSpace I) p).baseSet)
    (hsrc : ∀ t ∈ maximalSprayGeodesicInterval cov b p v,
      ∀ (γ : ℝ → M) (J : Set ℝ),
        IsSprayGeodesicOnWithInitial cov b γ J p v → γ t ∈ (chartAt H p).source) :
    IsOpen (maximalSprayGeodesicInterval cov b p v) ∧
      (0 : ℝ) ∈ maximalSprayGeodesicInterval cov b p v ∧
      maximalSprayGeodesic cov b p v 0 = p ∧
      (∀ t ∉ maximalSprayGeodesicInterval cov b p v, maximalSprayGeodesic cov b p v t = p) ∧
      (∀ t ∈ maximalSprayGeodesicInterval cov b p v, ∃ γ : ℝ → M, γ 0 = p ∧
        IsSprayGeodesicAt cov b γ 0 ∧ IsSprayGeodesicAt cov b γ t) := by
  refine ⟨maximalSprayGeodesicInterval_isOpen cov b p v,
    zero_mem_maximalSprayGeodesicInterval cov b p v hcov,
    maximalSprayGeodesic_zero cov b p v hcov,
    fun t ht => maximalSprayGeodesic_of_not_mem cov b ht, fun t ht => ?_⟩
  obtain ⟨γ, J, hJ, _hJconn, h0, htJ, hγ⟩ := id ht
  refine ⟨γ, hγ.start_eq, ?_, hγ.isSprayGeodesicAt (hJ.mem_nhds htJ) (hsrc t ht γ J hγ)⟩
  refine hγ.isSprayGeodesicAt (hJ.mem_nhds h0) ?_
  rw [hγ.start_eq]; exact mem_chart_source H p

end MaximalGeodesic

section ConstantGeodesic

/-- The fibre coordinate of the zero vector at `p`, read in the chart at `p`, is `0`. -/
theorem sprayFiberCoord_self_zero (p : M) :
    sprayFiberCoord (I := I) p (⟨p, (0 : E)⟩ : TangentBundle I M) = 0 := by
  have hp : p ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' p
  have hzero : (trivializationAt E (TangentSpace I) p)
      (⟨p, (0 : TangentSpace I p)⟩ : TangentBundle I M) = (p, 0) :=
    (trivializationAt E (TangentSpace I) p).zeroSection ℝ (x := p) hp
  change (trivializationAt E (TangentSpace I) p
    (⟨p, (0 : TangentSpace I p)⟩ : TangentBundle I M)).2 = 0
  rw [hzero]

/-- **The geodesic spray vanishes at the zero section** `⟨p, 0⟩` (chart basepoint =
foot, zero velocity): both spray components vanish, so the value is the zero tangent
vector.  This is what makes a stationary point a geodesic. -/
theorem geodesicVectorFieldChart_zero_section
    (cov : Connection I E (TangentSpace I : M → Type _)) (b : Basis ι ℝ E) (p : M) :
    geodesicVectorFieldChart cov b p (⟨p, (0 : E)⟩ : TangentBundle I M) = 0 := by
  classical
  have hcf : sprayFiberCoord (I := I) p (⟨p, (0 : E)⟩ : TangentBundle I M) = 0 :=
    sprayFiberCoord_self_zero p
  have hfiber : geodesicSprayFiber cov b p (⟨p, (0 : E)⟩ : TangentBundle I M) = (0, 0) := by
    simp only [geodesicSprayFiber, hcf, chartGamma_def, map_zero, Finsupp.coe_zero,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_smul, neg_zero]
  unfold geodesicVectorFieldChart
  rw [hfiber]
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨p, (0 : E)⟩ : TangentBundle I M)
  rw [← Bundle.Trivialization.coe_symmₗ (R := ℝ) e (⟨p, (0 : E)⟩ : TangentBundle I M)]
  exact map_zero _

/-- **Constant curves are geodesics** (Lee, §"Geodesics": a stationary curve is a
geodesic, immediate from the geodesic equation (4.16) with zero velocity).  The
constant lift `fun _ => ⟨p, 0⟩` is an integral curve of the geodesic spray because the
spray vanishes at the zero section, so `fun _ => p` is a spray geodesic at every time. -/
theorem isSprayGeodesicAt_const
    (cov : Connection I E (TangentSpace I : M → Type _)) (b : Basis ι ℝ E)
    (p : M) (t₀ : ℝ) :
    IsSprayGeodesicAt cov b (fun _ => p) t₀ := by
  refine ⟨p, fun _ => (⟨p, (0 : E)⟩ : TangentBundle I M), fun _ => rfl, ?_, ?_⟩
  · exact mem_chart_source H p
  · have hzero : geodesicVectorFieldChart cov b p (⟨p, (0 : E)⟩ : TangentBundle I M) = 0 :=
      geodesicVectorFieldChart_zero_section cov b p
    exact (isMIntegralCurve_const hzero).isMIntegralCurveAt t₀

end ConstantGeodesic

end

end LeeLib.Ch04
