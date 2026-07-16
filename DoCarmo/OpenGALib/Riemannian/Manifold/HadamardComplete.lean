import OpenGALib.Riemannian.Manifold.HadamardNonpos
import OpenGALib.Riemannian.Exponential.CInftyGlobal

/-!
# do Carmo Ch. 7 — the Cartan–Hadamard theorem, unconditionally

`HadamardNonpos.lean` assembled the Cartan–Hadamard theorem modulo the single hypothesis
`hsmooth : ContMDiff 𝓘(ℝ,E) I ∞ (expMapGlobal g hg p)`. That global `C^∞` smoothness of the
exponential map is now proved (`Riemannian.Exponential.contMDiff_expMapGlobal`), so this file
discharges `hsmooth` and states the theorem and its lemma **unconditionally**:

* `isLocalDiffeomorph_expMapGlobal_hadamard_of_nonpos_complete` — `lem:dc-ch7-3-2`: on a
  complete manifold of nonpositive curvature, `exp_p` is a `C^∞` local diffeomorphism;
* `hadamardDiffeomorphOfNonpos_complete` (+ `_coe`) — `thm:dc-ch7-3-1` (Cartan–Hadamard): a
  complete, simply connected manifold of nonpositive sectional curvature is diffeomorphic to
  `ℝⁿ` via `exp_p`.

Both are the `HadamardNonpos` versions with the `hsmooth` argument supplied by
`contMDiff_expMapGlobal`.

Blueprint: `thm:dc-ch7-3-1`, `lem:dc-ch7-3-2`.
Reference: do Carmo, *Riemannian Geometry*, Ch. 7, §3.
-/

open Set Filter
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

open Riemannian Riemannian.Geodesic Riemannian.Exponential Riemannian.HadamardModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M]

/-- **Math.** **do Carmo `lem:dc-ch7-3-2`, unconditionally.** On a complete manifold of
nonpositive curvature, `exp_p : T_pM → M` — as the map out of `HadamardModel E` — is a `C^∞`
local diffeomorphism. The global smoothness of `exp_p`
(`Riemannian.Exponential.contMDiff_expMapGlobal`) discharges the `hsmooth` hypothesis of
`isLocalDiffeomorph_expMapGlobal_hadamard_of_nonpos`. -/
theorem isLocalDiffeomorph_expMapGlobal_hadamard_of_nonpos_complete
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M)
    (hK : ∀ x : M, ∀ a c : TangentSpace I x,
      0 ≤ g.metricInner x (g.leviCivitaConnection.curvatureOperatorAt x a c c) a) :
    IsLocalDiffeomorph 𝓘(ℝ, E) I ∞
      (fun v : HadamardModel E => expMapGlobal (I := I) g hg p (HadamardModel.toModel v)) :=
  isLocalDiffeomorph_expMapGlobal_hadamard_of_nonpos g hg p
    (Riemannian.Exponential.contMDiff_expMapGlobal g hg p) hK

/-- **Math.** **do Carmo Ch. 7, Theorem 3.1 (Cartan–Hadamard), unconditionally.** Let `M` be a
complete, simply connected Riemannian manifold of nonpositive sectional curvature (`K ≤ 0`, in
the operator form `0 ≤ ⟨R(a,c)c, a⟩`). Then `exp_p : T_pM → M` is a **diffeomorphism**; in
particular `M` is diffeomorphic to `ℝⁿ`. The global smoothness of `exp_p`
(`Riemannian.Exponential.contMDiff_expMapGlobal`) discharges the `hsmooth` hypothesis of
`hadamardDiffeomorphOfNonpos`. -/
def hadamardDiffeomorphOfNonpos_complete
    [ConnectedSpace M] [SimplyConnectedSpace M] [LocPathConnectedSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M)
    (hK : ∀ x : M, ∀ a c : TangentSpace I x,
      0 ≤ g.metricInner x (g.leviCivitaConnection.curvatureOperatorAt x a c c) a) :
    Diffeomorph 𝓘(ℝ, E) I (HadamardModel E) M ∞ :=
  hadamardDiffeomorphOfNonpos g hg p (Riemannian.Exponential.contMDiff_expMapGlobal g hg p) hK

/-- **Math.** The unconditional Cartan–Hadamard diffeomorphism **is** `exp_p` itself
(anti-vacuity guard). -/
theorem hadamardDiffeomorphOfNonpos_complete_coe
    [ConnectedSpace M] [SimplyConnectedSpace M] [LocPathConnectedSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M)
    (hK : ∀ x : M, ∀ a c : TangentSpace I x,
      0 ≤ g.metricInner x (g.leviCivitaConnection.curvatureOperatorAt x a c c) a) :
    ⇑(hadamardDiffeomorphOfNonpos_complete g hg p hK)
      = fun v : HadamardModel E => expMapGlobal (I := I) g hg p (HadamardModel.toModel v) := rfl

end Riemannian.Jacobi

end
