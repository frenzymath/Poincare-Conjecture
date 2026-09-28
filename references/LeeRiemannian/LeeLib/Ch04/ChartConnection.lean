/-
Chapter 4, "Connections", §"Connections in the Tangent Bundle": the
**chart–Christoffel bridge**.

A local trivialization `e` of the tangent bundle `TM`, together with a basis `b`
of the model fibre `E`, induces a smooth local frame `(∂_i) = e.localFrame b` for
`TM` over the chart domain `e.baseSet` (mathlib's `Trivialization.localFrame`).
Reading an abstract tangent-bundle connection `∇` in this coordinate frame gives
Lee's **connection coefficients** in a chart, `Γ^k_{ij} : e.baseSet → ℝ`, defined
by

  `∇_{∂_i} ∂_j = Γ^k_{ij} ∂_k`   (Lee's equation (4.8)),

which are the Christoffel symbols of `∇` in the chart.  This file:

* packages `chartConnectionCoeff` = `connectionCoeff` for the trivialization frame;
* records the frame identity (4.8) for the chart frame;
* proves the genuinely new fact that each `Γ^k_{ij}` is **smooth** on `e.baseSet`,
  when the connection is `C¹`: `∇_{∂_i} ∂_j` is a `C¹` section (the connection is
  `C¹` and the frame sections are `C²`), and its frame coefficients are then `C¹`
  by mathlib's `Trivialization.contMDiffOn_baseSet_localFrame_coeff`.

This smoothness is what turns the Christoffel symbols into honest smooth functions
and unblocks the coordinate form of covariant differentiation along a curve,
geodesics, and parallel transport.
-/
import LeeLib.Ch04.ConnectionCoefficients
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

namespace LeeLib.Ch04

open Bundle Module
open scoped Manifold ContDiff Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*} [Fintype ι]
  {e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M)}
  [MemTrivializationAtlas e] {b : Basis ι ℝ E}

omit [FiniteDimensional ℝ E] [Fintype ι] in
/-- The smooth local frame `(∂_i)` for `TM` over the chart domain `e.baseSet`
induced by a trivialization `e` and a basis `b` of the model fibre: mathlib's
`Trivialization.localFrame`, packaged as an `IsLocalFrameOn`. -/
theorem chartFrame_isLocalFrameOn
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Basis ι ℝ E) :
    IsLocalFrameOn I E 1 (e.localFrame b) e.baseSet :=
  e.isLocalFrameOn_localFrame_baseSet I 1 b

/-- **Chart connection coefficients / Christoffel symbols** (Lee, equation (4.8)):
the connection coefficients `Γ^k_{ij}` of a tangent-bundle connection `∇` read in
the coordinate frame `(∂_i) = e.localFrame b` of a chart, defined on `e.baseSet`
(junk value `0` off it). -/
noncomputable def chartConnectionCoeff
    (cov : Connection I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Basis ι ℝ E) (i j k : ι) : M → ℝ :=
  connectionCoeff cov (e.isLocalFrameOn_localFrame_baseSet I 1 b) i j k

omit [FiniteDimensional ℝ E] in
/-- **Lee's equation (4.8) in a chart**: the defining relation of the chart
Christoffel symbols, `∇_{∂_i} ∂_j = Γ^k_{ij} ∂_k`, on the chart domain
`e.baseSet`. -/
theorem covariantDeriv_chartFrame_eq_sum_chartConnectionCoeff
    (cov : Connection I E (TangentSpace I : M → Type _)) (i j : ι) {x : M}
    (hx : x ∈ e.baseSet) :
    covariantDeriv cov (e.localFrame b i) (e.localFrame b j) x
      = ∑ k, chartConnectionCoeff cov e b i j k x • e.localFrame b k x :=
  covariantDeriv_frame_eq_sum_connectionCoeff cov
    (e.isLocalFrameOn_localFrame_baseSet I 1 b) i j hx

omit [FiniteDimensional ℝ E] [Fintype ι] in
/-- The frame identity `Γ^k_{ij}(x) = (∂_k)^*(∇_{∂_i} ∂_j)(x)`, expressing the chart
Christoffel symbol as the `k`-th frame coefficient of `∇_{∂_i} ∂_j`: it agrees
with mathlib's `Trivialization.localFrame_coeff`. -/
theorem chartConnectionCoeff_eq_localFrame_coeff
    (cov : Connection I E (TangentSpace I : M → Type _)) (i j k : ι) :
    chartConnectionCoeff cov e b i j k
      = (LinearMap.piApply (e.localFrame_coeff I b k))
          (covariantDeriv cov (e.localFrame b i) (e.localFrame b j)) := by
  funext x
  rfl

omit [FiniteDimensional ℝ E] [Fintype ι] in
/-- `∇_{∂_i} ∂_j` is a `C¹` section of `TM` over the chart domain `e.baseSet`,
whenever the connection is `C¹` there: the frame sections `∂_i, ∂_j` are `C²`
(the tangent bundle is smooth), so applying the `C¹` connection to them and
evaluating in the `C¹` frame direction gives a `C¹` section. -/
theorem contMDiffOn_covariantDeriv_chartFrame
    (cov : Connection I E (TangentSpace I : M → Type _))
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun e.baseSet) (i j : ι) :
    CMDiff[e.baseSet] 1 (T% (covariantDeriv cov (e.localFrame b i) (e.localFrame b j))) := by
  -- The section frame `∂_j` is `C²`, so `cov ∂_j` is a `C¹` section of `Hom(TM, TM)`.
  have h2 : (2 : ℕ∞ω) = 1 + 1 := by norm_num
  have hσ : CMDiff[e.baseSet] (1 + 1) (T% (e.localFrame b j)) :=
    h2 ▸ e.contMDiffOn_localFrame_baseSet 2 b j
  have hcovσ := hcov.contMDiff hσ
  -- The direction frame `∂_i` is `C¹`.
  have hX : CMDiff[e.baseSet] 1 (T% (e.localFrame b i)) :=
    e.contMDiffOn_localFrame_baseSet 1 b i
  -- Evaluate the `Hom`-bundle section against the vector field: `∇_{∂_i} ∂_j` is `C¹`.
  exact ContMDiffOn.clm_bundle_apply hcovσ hX

omit [Fintype ι] in
/-- **Smoothness of the chart Christoffel symbols** (the genuinely new part):
each chart connection coefficient `Γ^k_{ij}` is `C¹` on the chart domain
`e.baseSet`, whenever the connection is `C¹`.  `∇_{∂_i} ∂_j` is a `C¹` section
(`contMDiffOn_covariantDeriv_chartFrame`), so its coordinate coefficients in the
trivialization frame are `C¹` by
`Trivialization.contMDiffOn_baseSet_localFrame_coeff`. -/
theorem chartConnectionCoeff_contMDiffOn
    (cov : Connection I E (TangentSpace I : M → Type _))
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun e.baseSet) (i j k : ι) :
    CMDiff[e.baseSet] 1 (chartConnectionCoeff cov e b i j k) := by
  rw [chartConnectionCoeff_eq_localFrame_coeff]
  exact contMDiffOn_baseSet_localFrame_coeff b
    (contMDiffOn_covariantDeriv_chartFrame cov hcov i j) k

end LeeLib.Ch04
