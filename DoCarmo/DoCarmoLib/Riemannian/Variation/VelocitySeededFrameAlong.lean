import DoCarmoLib.Riemannian.Jacobi.CartanParallelFrame
import DoCarmoLib.Riemannian.Jacobi.MetricOrthoBasis
import DoCarmoLib.Riemannian.Jacobi.JacobiConstantCurvatureConjugate
import DoCarmoLib.Riemannian.Jacobi.ParallelTransport
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh1

/-!
# A manifold velocity-seeded parallel orthonormal frame along a geodesic

do Carmo, *Riemannian Geometry*, Ch. 9, §3 (Bonnet–Myers, `thm:dc-ch9-3-1`, and
Synge–Weinstein, `thm:dc-ch9-3-7`) both begin the same way: along a (minimizing) geodesic
`γ`, choose *parallel* orthonormal fields `e₁,…,e_{n-1}` orthogonal to `γ'`, together with
`e_n = γ'/|γ'|`.  This file supplies exactly that, at the manifold level.

`exists_velocitySeededParallelOrthoFrameAlongOn` produces a parallel orthonormal frame
`e : Fin n → ℝ → E` along `γ` whose distinguished member `e_{n₀}` is the *unit* velocity
`ℓ⁻¹·γ'` for all `t`, where `ℓ = |γ'|` is the (constant) speed.  The other `n − 1` members are
then automatically orthogonal to `γ'` at every `t`.

The chart-level analogue is `exists_velocitySeededParallelOrthoFrame`
(`Jacobi/VelocitySeededFrame.lean`), used in Ch. 8's E. Cartan theorem.  The manifold version
here crosses charts, which Bonnet–Myers needs because its geodesic (of length `> π r`) leaves
every chart.  It is assembled from three manifold-level ingredients:

* `exists_metricOrthonormalBasis_containing_unit` (`Jacobi/MetricOrthoBasis.lean`) — extend the
  unit velocity at `γ(a)` to a `g`-orthonormal basis of `T_{γ(a)}M`;
* `exists_parallelOrthoFrameAlongOn` (`Jacobi/CartanParallelFrame.lean`) — parallel-transport
  that basis, keeping it orthonormal at every `t`;
* `isParallelFieldAlongOn_velocity` + `IsParallelFieldAlongOn.eqOn_of_initial` — the velocity
  `γ'` is itself a parallel field, so by uniqueness of parallel transport the distinguished
  transported member, which starts equal to `ℓ⁻¹·γ'(a)`, stays equal to `ℓ⁻¹·γ'(t)`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 9, §3 (proofs of Thm. 3.1 and Thm. 3.7).
-/

open Set Riemannian
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Riemannian.Variation

open Riemannian.Jacobi Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **A velocity-seeded parallel orthonormal frame along a geodesic** (do Carmo
Ch. 9, §3).  Along a regular geodesic `γ : [a, b] → M` (velocity `γ'(a) ≠ 0`), there is a
parallel orthonormal frame `e₁,…,eₙ` and a distinguished index `n₀` with `e_{n₀}(t)` the unit
velocity `ℓ⁻¹·γ'(t)` for all `t`, where `ℓ = |γ'| > 0` is the constant speed.  Concretely:

* each `e i` is parallel along `γ` (`Dₑᵢ/dt = 0`);
* `{e i(t)}` is `g`-orthonormal at every `t ∈ [a, b]`;
* `e n₀(t) = ℓ⁻¹ · γ'(t)` (do Carmo's `e_n = γ'/|γ'|`), hence for `i ≠ n₀`, `e i(t) ⟂ γ'(t)`.

Construction: extend the unit velocity `ℓ⁻¹·γ'(a)` to a `g`-orthonormal basis of `T_{γ(a)}M`
(`exists_metricOrthonormalBasis_containing_unit`), parallel-transport it
(`exists_parallelOrthoFrameAlongOn`), and identify the distinguished member with `ℓ⁻¹·γ'` by
uniqueness of parallel transport (`IsParallelFieldAlongOn.eqOn_of_initial`), since `γ'` is
itself parallel (`isParallelFieldAlongOn_velocity`). -/
theorem exists_velocitySeededParallelOrthoFrameAlongOn
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgeo : Riemannian.Geodesic.IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hvel : DCVelocity (I := I) γ a ≠ 0) :
    ∃ (e : Fin (Module.finrank ℝ E) → ℝ → E) (n₀ : Fin (Module.finrank ℝ E)) (ℓ : ℝ),
      0 < ℓ ∧
      (∀ i, IsParallelFieldAlongOn (I := I) g γ (e i) a b) ∧
      (∀ t ∈ Icc a b, ∀ i j, g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
        = if i = j then (1 : ℝ) else 0) ∧
      (∀ t ∈ Icc a b, e n₀ t = ℓ⁻¹ • DCVelocity (I := I) γ t) := by
  classical
  -- the velocity field and its (positive) squared speed at `a`
  set vel : ℝ → E := fun τ => mfderiv 𝓘(ℝ, ℝ) I γ τ 1 with hveldef
  have hvelA : vel a = DCVelocity (I := I) γ a := rfl
  have hsqpos : 0 < g.metricInner (γ a) (vel a) (vel a) :=
    g.metricInner_self_pos (γ a) (vel a) (hvelA ▸ hvel)
  set ℓ : ℝ := Real.sqrt (g.metricInner (γ a) (vel a) (vel a)) with hℓdef
  have hℓpos : 0 < ℓ := Real.sqrt_pos.mpr hsqpos
  have hℓsq : ℓ * ℓ = g.metricInner (γ a) (vel a) (vel a) := Real.mul_self_sqrt hsqpos.le
  -- the unit velocity `u = ℓ⁻¹ • γ'(a)`
  set u : E := ℓ⁻¹ • vel a with hudef
  have hu : g.metricInner (γ a) u u = 1 := by
    have hℓne : ℓ ≠ 0 := hℓpos.ne'
    rw [hudef, g.metricInner_smul_left, g.metricInner_smul_right, ← hℓsq]
    field_simp
  -- extend `u` to a `g`-orthonormal basis at `γ(a)`
  obtain ⟨e₀, n₀, he₀n₀, horth₀⟩ :=
    exists_metricOrthonormalBasis_containing_unit (I := I) g (γ a) hu
  -- parallel-transport the basis along `γ`
  obtain ⟨e, hea, hepar, heorth⟩ :=
    exists_parallelOrthoFrameAlongOn (I := I) hab hgeo hγc e₀ horth₀
  refine ⟨e, n₀, ℓ, hℓpos, hepar, heorth, ?_⟩
  -- the distinguished member equals `ℓ⁻¹ • γ'` by uniqueness of parallel transport
  have hvelpar : IsParallelFieldAlongOn (I := I) g γ vel a b :=
    isParallelFieldAlongOn_velocity g hab hgeo hγc
  have hsmulpar : IsParallelFieldAlongOn (I := I) g γ (fun τ => ℓ⁻¹ • vel τ) a b :=
    hvelpar.smul ℓ⁻¹
  have hinit : e n₀ a = (fun τ => ℓ⁻¹ • vel τ) a := by
    rw [hea n₀, he₀n₀, hudef]
  exact IsParallelFieldAlongOn.eqOn_of_initial hab.le (hepar n₀) hsmulpar hgeo hγc hinit

end Riemannian.Variation

end
