import OpenGALib.Riemannian.Geodesic.Equation
import OpenGALib.Riemannian.Exponential.Defs

/-!
# Geodesics and the exponential map — Jacobi-port aliases

Ported into OpenGALib from the Morgan–Tian / Poincaré Ch.1, §1.2 development
(toward `cor:dc-ch5-2-5`). Provides the `Riemannian.Jacobi`-namespace aliases of
OpenGALib's geodesic and exponential-map interfaces that the ported Jacobi-field
manifold layer is written against.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.2.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A curve `γ : ℝ → M` is a **geodesic** of `g` if `∇_{γ̇} γ̇ = 0`
everywhere. Alias of `Riemannian.Geodesic.IsGeodesic`. -/
abbrev IsGeodesic (g : Riemannian.RiemannianMetric I M) (γ : ℝ → M) : Prop :=
  Riemannian.Geodesic.IsGeodesic (I := I) g γ

/-- **Math.** A curve `γ : ℝ → M` is a **geodesic** of `g` on the set `s ⊆ ℝ`
if `∇_{γ̇} γ̇ = 0` at every `t ∈ s`. Alias of
`Riemannian.Geodesic.IsGeodesicOn`. -/
abbrev IsGeodesicOn (g : Riemannian.RiemannianMetric I M) (γ : ℝ → M)
    (s : Set ℝ) : Prop :=
  Riemannian.Geodesic.IsGeodesicOn (I := I) g γ s

/-- **Math.** The **exponential map** at `p ∈ M`, `exp_p(v) = γ_v(1)`. Alias of
`Riemannian.Exponential.expMap`. -/
abbrev expMap (g : Riemannian.RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : M :=
  Riemannian.Exponential.expMap (I := I) g p v

/-- **Math.** The maximal domain `O_p ⊆ T_pM` of `expMap g p`. Alias of
`Riemannian.Exponential.expDomain`. -/
abbrev expDomain (g : Riemannian.RiemannianMetric I M) (p : M) :
    Set (TangentSpace I p) :=
  Riemannian.Exponential.expDomain (I := I) g p

end Riemannian.Jacobi

end
