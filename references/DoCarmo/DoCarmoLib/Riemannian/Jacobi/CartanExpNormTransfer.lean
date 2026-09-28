import DoCarmoLib.Riemannian.Jacobi.JacobiConstCurvatureNorm
import DoCarmoLib.Riemannian.Jacobi.ExpLocalDiffeo

/-!
# do Carmo Ch. 8, §2 — the differential of `exp` is norm-preserving between spaces of the
same constant curvature

This file joins the two halves of the isometry claim in E. Cartan's theorem
(`thm:dc-ch8-2-1`), in the same-curvature case used by `cor:dc-ch8-2-2` /
`cor:dc-ch8-2-3` / `thm:dc-ch8-4-1`:

* the **analytic half** — `metricInner_jacobiField_transfer_of_constantCurvature`
  (`JacobiConstCurvatureNorm.lean`): on two manifolds of the *same* constant sectional
  curvature `K₀`, two Jacobi fields vanishing at `t = 0` along unit-speed geodesics whose
  initial covariant derivatives have matching scalar invariants have **equal norms** at
  every time;
* the **exponential half** — `hasFDerivAt_chartReading_expMapGlobal` (= `cor:dc-ch5-2-5`,
  `ExpDifferential.lean`): `d(exp_p)_v (Z) = Y_Z(1)`, the value at time `1` of the Jacobi
  field along `γ_v` with `Y_Z(0) = 0`, `∇Y_Z(0) = Z`.

Composing them gives the statement that actually feeds Cartan's corollaries: with
`f = exp_{p̃} ∘ i ∘ exp_p⁻¹` for a linear isometry `i`, the differential `df` is
**norm-preserving**, because `d(exp_p)_v(Z)` and `d(exp_{p̃})_{i v}(i Z)` are the endpoint
values of two Jacobi fields with matching invariants, hence have the same norm.

## Mathematics

Let `v` be a **nonzero** vector at `p` and `ṽ = i v` the corresponding vector at `p̃`. The
geodesics `γ_v` and `γ_ṽ` then have the *same* squared speed `c = |v|² = |ṽ|² ≠ 0`
(`speedSq_globalGeodesic`, and `i` is a linear isometry), so the general-speed
constant-curvature norm formula applies to both. For `Z` at `p` and `Z̃ = i Z` at `p̃`, the
linear isometry `i` preserves the two scalar invariants `⟨Z, v⟩` and `|Z|²` that the norm
formula depends on, whence

  `|d(exp_{p̃})_{ṽ} (Z̃)| = |Ỹ_{Z̃}(1)| = |Y_Z(1)| = |d(exp_p)_v (Z)|`.

Both differentials are read in charts (`ζ`, `ζ̃`) around the endpoints `exp_p(v)`,
`exp_{p̃}(ṽ)`, so the norms are measured with the **chart Gram form** `chartMetricInner`
there; `chartMetricInner_chartVectorRep_eq_metricInner` is the bridge identifying that
chart norm with the intrinsic one.

## Contents

* `mfderiv_globalGeodesic_zero` — the intrinsic initial velocity of `γ_v` is `v`.
* `speedSq_globalGeodesic` — `γ_v` has constant speed `|v|²`, the value the general-speed
  norm formula is parametrized by.
* `chartMetricInner_chartVectorRep_eq_metricInner` — the chart-Gram norm of the chart
  reading of a tangent vector is its intrinsic norm.
* `chartMetricInner_expDifferential_eq_metricInner_jacobiField` — the chart norm of
  `d(exp_p)_v(Z)` is the intrinsic norm `|Y_Z(1)|`.
* `chartMetricInner_expDifferential_transfer_of_constantCurvature_of_speedSq` — **the
  transfer**: matching invariants across two same-`K₀` manifolds ⟹ the two exponential
  differentials have equal norms, for any **nonzero** `v` (not just `|v| = 1`), which is
  what `cor:dc-ch8-2-2` needs — it must reach every `q = exp_p(v)` in a *ball* around `p`,
  not just the unit sphere. This is the norm-preservation (hence isometry) step of Cartan's
  theorem, `φ_t`-free. `chartMetricInner_expDifferential_transfer_of_constantCurvature` is
  its `|v| = 1` specialization.
* `expDifferential_isEquiv_jacobi_of_not_conjugate` — the `E ≃L[ℝ] E` form of
  `d(exp_p)_v` *together with* the Jacobi identification clause, the shape the assembly
  of `cor:dc-ch8-2-2` consumes.

Blueprint: `lem:dc-ch8-2-1-exp-norm-transfer`, feeding `cor:dc-ch8-2-2`, `cor:dc-ch8-2-3`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 8, §2.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-! ### The initial velocity and the speed of `γ_v` -/

/-- **Math.** The intrinsic initial velocity of the global geodesic `γ_v` is `v` itself.
By construction `γ_v` reads in the chart at `p` as a curve with coordinate velocity `v` at
time `0` (`hasDerivAt_chartReading_globalGeodesic`); the velocity readback
`mfderiv_eq_of_hasDerivAt_extChartAt` converts that to the intrinsic velocity, and the
coordinate change from the chart at `p` to itself is the identity. -/
theorem mfderiv_globalGeodesic_zero (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : E) :
    mfderiv 𝓘(ℝ, ℝ) I (globalGeodesic (I := I) g hg p v) 0 1 = v := by
  have hd : HasDerivAt (fun s => extChartAt I p (globalGeodesic (I := I) g hg p v s)) v 0 :=
    hasDerivAt_chartReading_globalGeodesic (I := I) g hg p v
  have h0 : globalGeodesic (I := I) g hg p v 0 = p := globalGeodesic_zero g hg p v
  have hsrc : globalGeodesic (I := I) g hg p v 0 ∈ (chartAt H p).source := by
    rw [h0]; exact mem_chart_source H p
  rw [mfderiv_eq_of_hasDerivAt_extChartAt (I := I)
    (continuous_globalGeodesic g hg p v).continuousAt hsrc hd, h0]
  exact tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) p)

/-- **Math.** **do Carmo Ch. 3, §2: geodesics have constant speed** — for the global
geodesic `γ_v` the constant is `|v|²`, measured at `p`. Constancy is
`IsGeodesicOn.speedSq_eq` on the open connected set `univ`, and the value at time `0` is
`⟨v, v⟩_p` by `mfderiv_globalGeodesic_zero`.

In particular a **unit** `v` (`⟨v,v⟩_p = 1`) makes `γ_v` unit-speed — exactly the
hypothesis `metricInner_jacobiField_eq_of_constantCurvature` requires. -/
theorem speedSq_globalGeodesic (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : E) (τ : ℝ) :
    speedSq (I := I) g (globalGeodesic (I := I) g hg p v) τ = g.metricInner p v v := by
  have hgeoOn : IsGeodesicOn (I := I) g (globalGeodesic (I := I) g hg p v) (univ : Set ℝ) :=
    fun t _ => isGeodesic_globalGeodesic g hg p v t
  have hcont : ContinuousOn (globalGeodesic (I := I) g hg p v) (univ : Set ℝ) :=
    (continuous_globalGeodesic g hg p v).continuousOn
  rw [hgeoOn.speedSq_eq isOpen_univ isPreconnected_univ hcont (mem_univ τ) (mem_univ (0 : ℝ)),
    speedSq_def, mfderiv_globalGeodesic_zero, globalGeodesic_zero]

/-! ### The chart-Gram norm of a chart reading is the intrinsic norm -/

/-- **Math.** **A chart reading of a tangent vector has the same norm as the vector.**
The chart-`ζ` Gram form `chartMetricInner g ζ` evaluated at the chart point
`extChartAt I ζ x` on the chart reading `tangentCoordChange I x ζ x w` of `w ∈ T_x M`
returns the intrinsic `⟨w, w⟩_x`. This is the bridge that lets the constant-curvature norm
formula (stated intrinsically) speak about the chart-read differential of `exp`. -/
theorem chartMetricInner_chartVectorRep_eq_metricInner (g : RiemannianMetric I M) (ζ : M)
    {x : M} (hx : x ∈ (chartAt H ζ).source) (w w' : E) :
    chartMetricInner (I := I) g ζ (extChartAt I ζ x)
        (tangentCoordChange I x ζ x w) (tangentCoordChange I x ζ x w')
      = g.metricInner x w w' := by
  rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g ζ hx,
    trivializationAt_symm_eq_tangentCoordChange (I := I) ζ hx,
    trivializationAt_symm_eq_tangentCoordChange (I := I) ζ hx,
    tangentCoordChange_realize_comp (I := I) (mem_chart_source H x) hx,
    tangentCoordChange_realize_comp (I := I) (mem_chart_source H x) hx,
    tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) x),
    tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) x)]

/-! ### The norm of the exponential differential is the norm of a Jacobi field -/

/-- **Math.** **`|d(exp_p)_v(Z)| = |Y_Z(1)|`.** Combining `cor:dc-ch5-2-5`
(`hasFDerivAt_chartReading_expMapGlobal`: the chart-`ζ` differential of `exp_p` at `v`
sends `Z` to the chart reading of `Y_Z(1)`) with
`chartMetricInner_chartVectorRep_eq_metricInner` (the chart reading is norm-faithful):
the chart-Gram norm of `d(exp_p)_v(Z)` at the endpoint is the intrinsic norm of the Jacobi
field `Y_Z` at time `1`.

This is the form in which the constant-curvature norm formula can be applied to the
differential of `exp`. -/
theorem chartMetricInner_expDifferential_eq_metricInner_jacobiField
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) (v : E)
    {ζ : M} {D : E →L[ℝ] E}
    (hζ : expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source)
    (hjac : ∀ J DJ : ℝ → E,
      IsJacobiFieldAlongOn (I := I) g (globalGeodesic (I := I) g hg p v) J DJ 0 1 →
      J 0 = 0 →
      D (DJ 0) = chartVectorRep (I := I) (globalGeodesic (I := I) g hg p v) ζ J 1)
    (J DJ : ℝ → E)
    (hJ : IsJacobiFieldAlongOn (I := I) g (globalGeodesic (I := I) g hg p v) J DJ 0 1)
    (hJ0 : J 0 = 0) :
    chartMetricInner (I := I) g ζ (extChartAt I ζ (expMapGlobal (I := I) g hg p v))
        (D (DJ 0)) (D (DJ 0))
      = g.metricInner (globalGeodesic (I := I) g hg p v 1) (J 1) (J 1) := by
  have hend : globalGeodesic (I := I) g hg p v 1 = expMapGlobal (I := I) g hg p v := rfl
  rw [hjac J DJ hJ hJ0]
  show chartMetricInner (I := I) g ζ (extChartAt I ζ (expMapGlobal (I := I) g hg p v))
      (tangentCoordChange I (globalGeodesic (I := I) g hg p v 1) ζ
        (globalGeodesic (I := I) g hg p v 1) (J 1))
      (tangentCoordChange I (globalGeodesic (I := I) g hg p v 1) ζ
        (globalGeodesic (I := I) g hg p v 1) (J 1)) = _
  rw [hend]
  exact chartMetricInner_chartVectorRep_eq_metricInner (I := I) g ζ hζ (J 1) (J 1)

/-! ### The transfer between two spaces of the same constant curvature -/

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {M' : Type*} [MetricSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [I'.Boundaryless] [SigmaCompactSpace M'] [T2Space M']

/-- **Math.** **do Carmo Ch. 8, `thm:dc-ch8-2-1` — the norm-preservation step, at the level
of the exponential differential, in constant curvature.**

Let `M`, `M'` both have constant sectional curvature `K₀` and be complete. Let `v` be a
**unit** vector at `p ∈ M` and `ṽ` a unit vector at `p̃ ∈ M'`, and let `Z`, `Z̃` be tangent
vectors whose scalar invariants match:

* `⟨Z̃, ṽ⟩_{p̃} = ⟨Z, v⟩_p`,
* `|Z̃|²_{p̃} = |Z|²_p`.

Then the two exponential differentials have **equal norms**, measured with the chart Gram
form at the respective endpoints:

  `|d(exp_{p̃})_{ṽ} (Z̃)| = |d(exp_p)_v (Z)|`.

For `f = exp_{p̃} ∘ i ∘ exp_p⁻¹` with `i` a linear isometry and `ṽ = i v`, `Z̃ = i Z`, both
invariants are preserved by `i` automatically, so `df` is norm-preserving — the isometry
claim of E. Cartan's theorem in the same-curvature case, requiring **no** parallel-transport
conjugation `φ_t`.

Proof: `cor:dc-ch5-2-5` identifies each side with the norm of a Jacobi field vanishing at
`0` (`chartMetricInner_expDifferential_eq_metricInner_jacobiField`); the geodesics `γ_v`,
`γ_ṽ` are unit-speed (`speedSq_globalGeodesic`), so
`metricInner_jacobiField_transfer_of_constantCurvature` equates the two norms. -/
theorem chartMetricInner_expDifferential_transfer_of_constantCurvature_of_speedSq
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (g' : RiemannianMetric I' M') (hg' : g'.IsRiemannianDist) [CompleteSpace M']
    {K₀ c : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    (hK' : g'.leviCivitaConnection.IsConstantCurvature g' K₀)
    (p : M) (p' : M') (v v' Z Z' : E) (hvne : v ≠ 0)
    (hv : g.metricInner p v v = c) (hv' : g'.metricInner p' v' v' = c)
    (hmatch_a : g'.metricInner p' Z' v' = g.metricInner p Z v)
    (hmatch_n : g'.metricInner p' Z' Z' = g.metricInner p Z Z)
    {ζ : M} {D : E →L[ℝ] E}
    (hζ : expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source)
    (hjac : ∀ J DJ : ℝ → E,
      IsJacobiFieldAlongOn (I := I) g (globalGeodesic (I := I) g hg p v) J DJ 0 1 →
      J 0 = 0 →
      D (DJ 0) = chartVectorRep (I := I) (globalGeodesic (I := I) g hg p v) ζ J 1)
    {ζ' : M'} {D' : E →L[ℝ] E}
    (hζ' : expMapGlobal (I := I') g' hg' p' v' ∈ (chartAt H' ζ').source)
    (hjac' : ∀ J DJ : ℝ → E,
      IsJacobiFieldAlongOn (I := I') g' (globalGeodesic (I := I') g' hg' p' v') J DJ 0 1 →
      J 0 = 0 →
      D' (DJ 0) = chartVectorRep (I := I') (globalGeodesic (I := I') g' hg' p' v') ζ' J 1)
    (h Dh : ℝ → ℝ) (hd1 : ∀ t, HasDerivAt h (Dh t) t)
    (hd2 : ∀ t, HasDerivAt Dh (-(K₀ * c) * h t) t) (h0 : h 0 = 0) (Dh0 : Dh 0 = 1) :
    chartMetricInner (I := I') g' ζ' (extChartAt I' ζ' (expMapGlobal (I := I') g' hg' p' v'))
        (D' Z') (D' Z')
      = chartMetricInner (I := I) g ζ (extChartAt I ζ (expMapGlobal (I := I) g hg p v))
        (D Z) (D Z) := by
  classical
  -- positive definiteness turns `v ≠ 0` into the nondegeneracy `c ≠ 0` the norm formula needs
  have hc : c ≠ 0 := by
    rw [← hv]; exact ne_of_gt (g.metricInner_self_pos p (v : TangentSpace I p) hvne)
  set γ : ℝ → M := globalGeodesic (I := I) g hg p v with hγdef
  set γ' : ℝ → M' := globalGeodesic (I := I') g' hg' p' v' with hγ'def
  -- the two geodesics, their continuity and their unit speed
  have hγ0 : γ 0 = p := globalGeodesic_zero g hg p v
  have hγ'0 : γ' 0 = p' := globalGeodesic_zero g' hg' p' v'
  have hgeo : IsGeodesicOn (I := I) g γ (Icc 0 1) := fun t _ =>
    isGeodesic_globalGeodesic g hg p v t
  have hgeo' : IsGeodesicOn (I := I') g' γ' (Icc 0 1) := fun t _ =>
    isGeodesic_globalGeodesic g' hg' p' v' t
  have hγc : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt γ t := fun t _ =>
    (continuous_globalGeodesic g hg p v).continuousAt
  have hγc' : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt γ' t := fun t _ =>
    (continuous_globalGeodesic g' hg' p' v').continuousAt
  have hspeed : ∀ τ ∈ Icc (0 : ℝ) 1, speedSq (I := I) g γ τ = c := fun τ _ => by
    rw [hγdef, speedSq_globalGeodesic]; exact hv
  have hspeed' : ∀ τ ∈ Icc (0 : ℝ) 1, speedSq (I := I') g' γ' τ = c := fun τ _ => by
    rw [hγ'def, speedSq_globalGeodesic]; exact hv'
  -- the Jacobi fields with initial data `(0, Z)` resp. `(0, Z')`
  obtain ⟨J, DJ, hJ, hJ0, hDJ0⟩ :=
    exists_isJacobiFieldAlongOn (I := I) (g := g) (γ := γ) (a := 0) (b := 1) zero_lt_one
      hgeo hγc (0 : TangentSpace I (γ 0)) (Z : TangentSpace I (γ 0))
  obtain ⟨Jt, DJt, hJt, hJt0, hDJt0⟩ :=
    exists_isJacobiFieldAlongOn (I := I') (g := g') (γ := γ') (a := 0) (b := 1) zero_lt_one
      hgeo' hγc' (0 : TangentSpace I' (γ' 0)) (Z' : TangentSpace I' (γ' 0))
  have hJ0' : J 0 = 0 := hJ0
  have hJt0' : Jt 0 = 0 := hJt0
  have hDJ0' : DJ 0 = Z := hDJ0
  have hDJt0' : DJt 0 = Z' := hDJt0
  -- the two exponential differentials are the endpoint values of these Jacobi fields
  have hleft : chartMetricInner (I := I) g ζ
      (extChartAt I ζ (expMapGlobal (I := I) g hg p v)) (D Z) (D Z)
      = g.metricInner (γ 1) (J 1) (J 1) := by
    rw [← hDJ0']
    exact chartMetricInner_expDifferential_eq_metricInner_jacobiField (I := I) g hg p v
      hζ hjac J DJ hJ hJ0'
  have hright : chartMetricInner (I := I') g' ζ'
      (extChartAt I' ζ' (expMapGlobal (I := I') g' hg' p' v')) (D' Z') (D' Z')
      = g'.metricInner (γ' 1) (Jt 1) (Jt 1) := by
    rw [← hDJt0']
    exact chartMetricInner_expDifferential_eq_metricInner_jacobiField (I := I') g' hg' p' v'
      hζ' hjac' Jt DJt hJt hJt0'
  rw [hleft, hright]
  -- the initial invariants match, so the constant-curvature norm formula transfers
  refine metricInner_jacobiField_transfer_of_constantCurvature_of_speedSq (I := I) (I' := I') g g'
    hK hK' zero_lt_one hgeo hγc hspeed hgeo' hγc' hspeed' hc J DJ hJ hJ0' Jt DJt hJt hJt0'
    ?_ ?_ h Dh hd1 hd2 h0 Dh0 (right_mem_Icc.mpr zero_le_one)
  · rw [hDJt0', hDJ0', hγ'def, hγdef, mfderiv_globalGeodesic_zero, mfderiv_globalGeodesic_zero,
      globalGeodesic_zero, globalGeodesic_zero]
    exact hmatch_a
  · rw [hDJt0', hDJ0', hγ'def, hγdef, globalGeodesic_zero, globalGeodesic_zero]
    exact hmatch_n

/-- **Math.** **do Carmo Ch. 8, `thm:dc-ch8-2-1` — the norm-preservation step** — the
unit-speed (`c = 1`) specialization of
`chartMetricInner_expDifferential_transfer_of_constantCurvature_of_speedSq`. -/
theorem chartMetricInner_expDifferential_transfer_of_constantCurvature
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (g' : RiemannianMetric I' M') (hg' : g'.IsRiemannianDist) [CompleteSpace M']
    {K₀ : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    (hK' : g'.leviCivitaConnection.IsConstantCurvature g' K₀)
    (p : M) (p' : M') (v v' Z Z' : E)
    (hv : g.metricInner p v v = 1) (hv' : g'.metricInner p' v' v' = 1)
    (hmatch_a : g'.metricInner p' Z' v' = g.metricInner p Z v)
    (hmatch_n : g'.metricInner p' Z' Z' = g.metricInner p Z Z)
    {ζ : M} {D : E →L[ℝ] E}
    (hζ : expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source)
    (hjac : ∀ J DJ : ℝ → E,
      IsJacobiFieldAlongOn (I := I) g (globalGeodesic (I := I) g hg p v) J DJ 0 1 →
      J 0 = 0 →
      D (DJ 0) = chartVectorRep (I := I) (globalGeodesic (I := I) g hg p v) ζ J 1)
    {ζ' : M'} {D' : E →L[ℝ] E}
    (hζ' : expMapGlobal (I := I') g' hg' p' v' ∈ (chartAt H' ζ').source)
    (hjac' : ∀ J DJ : ℝ → E,
      IsJacobiFieldAlongOn (I := I') g' (globalGeodesic (I := I') g' hg' p' v') J DJ 0 1 →
      J 0 = 0 →
      D' (DJ 0) = chartVectorRep (I := I') (globalGeodesic (I := I') g' hg' p' v') ζ' J 1)
    (h Dh : ℝ → ℝ) (hd1 : ∀ t, HasDerivAt h (Dh t) t)
    (hd2 : ∀ t, HasDerivAt Dh (-K₀ * h t) t) (h0 : h 0 = 0) (Dh0 : Dh 0 = 1) :
    chartMetricInner (I := I') g' ζ' (extChartAt I' ζ' (expMapGlobal (I := I') g' hg' p' v'))
        (D' Z') (D' Z')
      = chartMetricInner (I := I) g ζ (extChartAt I ζ (expMapGlobal (I := I) g hg p v))
        (D Z) (D Z) := by
  -- `v` is nonzero because `⟨v,v⟩ = 1 ≠ 0`; the `0` must be typed in `TangentSpace I p`,
  -- since `metricInner_zero_left` does not fire on an `E`-typed `0` (semireducibility)
  have hvne : v ≠ 0 := by
    intro hzero
    rw [hzero] at hv
    exact zero_ne_one ((g.metricInner_zero_left p (0 : TangentSpace I p)).symm.trans hv)
  exact chartMetricInner_expDifferential_transfer_of_constantCurvature_of_speedSq
    (I := I) (I' := I') g hg g' hg' hK hK' p p' v v' Z Z' hvne hv hv' hmatch_a hmatch_n
    hζ hjac hζ' hjac' h Dh hd1 (by simpa using hd2) h0 Dh0

/-! ### The isomorphism form of `d(exp_p)_v`, with the Jacobi clause -/

/-- **Math.** **`d(exp_p)_v` is a continuous linear isomorphism, *with* the Jacobi
identification.** This is `expDifferential_isEquiv_of_not_conjugate` (do Carmo
`lem:dc-ch7-3-2`, analytic core) strengthened to retain the clause
`D (DJ 0) = ` chart reading of `J 1` of `cor:dc-ch5-2-5` — the two facts are produced by the
*same* underlying `hasStrictFDerivAt_chartReading_expMapGlobal`, but the existing packaging
drops the Jacobi clause, and the assembly of `cor:dc-ch8-2-2` needs both at once: the
isomorphism to invert `d(exp_p)` (so that every tangent vector at `q = exp_p(v)` is the
endpoint of a Jacobi field), and the Jacobi clause to compute norms.

Blueprint: `lem:dc-ch7-3-2`, `cor:dc-ch5-2-5`. -/
theorem expDifferential_isEquiv_jacobi_of_not_conjugate
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {v : E}
    (hnc : ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p v) 1) :
    ∃ (ζ : M) (D : E ≃L[ℝ] E),
      expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source ∧
      HasStrictFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w))
        (D : E →L[ℝ] E) v ∧
      (∀ J DJ : ℝ → E,
        IsJacobiFieldAlongOn (I := I) g (globalGeodesic (I := I) g hg p v) J DJ 0 1 →
        J 0 = 0 →
        (D : E →L[ℝ] E) (DJ 0)
          = chartVectorRep (I := I) (globalGeodesic (I := I) g hg p v) ζ J 1) := by
  classical
  obtain ⟨α, ζ, D, _hpα, hζ, hFD, hjac⟩ :=
    hasStrictFDerivAt_chartReading_expMapGlobal (I := I) g hg p v
  have hinj : Function.Injective D :=
    (expDifferential_injective_iff_not_conjugate (I := I) g hg p v hζ hjac).2 hnc
  have hsurj : Function.Surjective (D : E →ₗ[ℝ] E) :=
    LinearMap.injective_iff_surjective.mp hinj
  refine ⟨ζ, (LinearEquiv.ofBijective (D : E →ₗ[ℝ] E) ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
    hζ, ?_, ?_⟩
  · have hcoe : (((LinearEquiv.ofBijective (D : E →ₗ[ℝ] E) ⟨hinj, hsurj⟩).toContinuousLinearEquiv :
        E ≃L[ℝ] E) : E →L[ℝ] E) = D := by ext w; rfl
    rw [hcoe]; exact hFD
  · intro J DJ hJ hJ0
    have hcoe : (((LinearEquiv.ofBijective (D : E →ₗ[ℝ] E) ⟨hinj, hsurj⟩).toContinuousLinearEquiv :
        E ≃L[ℝ] E) : E →L[ℝ] E) = D := by ext w; rfl
    rw [hcoe]; exact hjac J DJ hJ hJ0

end Riemannian.Jacobi

end
