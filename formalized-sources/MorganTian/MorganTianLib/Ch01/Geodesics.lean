import DoCarmoLib.Riemannian.Geodesic.Equation
import DoCarmoLib.Riemannian.Exponential.Defs
import MorganTianLib.Ch01.Metric

/-!
# Poincaré Ch. 1, §1.2 — Geodesics and the exponential map

Restates Morgan–Tian's definition of a geodesic (blueprint `def:geodesic`) and
of the exponential map (blueprint `def:exponential-map`) as aliases for
DoCarmoLib's geodesic and exponential-map interfaces.

Morgan–Tian define a geodesic on an open interval `I ⊆ ℝ` by
`∇_{γ̇} γ̇ = 0`; DoCarmoLib's `IsGeodesicOn g γ s` is the analogous
set-relativised notion (for `s` an interval this matches the blueprint
exactly), while `IsGeodesic g γ` is the special case `s = Set.univ`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.2
(blueprint `def:geodesic`, `def:exponential-map`).
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A curve `γ : ℝ → M` is a **geodesic** of `g` if it satisfies
`∇_{γ̇} γ̇ = 0` at every time `t`. Alias of `Riemannian.Geodesic.IsGeodesic`.

Blueprint: `def:geodesic` (the global, all-of-`ℝ` case of the blueprint's
"open interval" definition; see `IsGeodesicOn` for the interval-relativised
statement). -/
abbrev IsGeodesic (g : Riemannian.RiemannianMetric I M) (γ : ℝ → M) : Prop :=
  Riemannian.Geodesic.IsGeodesic (I := I) g γ

/-- **Math.** A curve `γ : ℝ → M` is a **geodesic** of `g` on the set `s ⊆ ℝ`
if it satisfies `∇_{γ̇} γ̇ = 0` at every time `t ∈ s`. Alias of
`Riemannian.Geodesic.IsGeodesicOn`. Taking `s` to be an open interval `J`
recovers Morgan–Tian's `def:geodesic` verbatim: "let `J` be an open interval;
a smooth curve `γ : J → M` is a geodesic if `∇_{γ̇} γ̇ = 0`."

Blueprint: `def:geodesic`. -/
abbrev IsGeodesicOn (g : Riemannian.RiemannianMetric I M) (γ : ℝ → M)
    (s : Set ℝ) : Prop :=
  Riemannian.Geodesic.IsGeodesicOn (I := I) g γ s

/-- **Math.** The **exponential map** at `p ∈ M`, `exp_p(v) = γ_v(1)`, the
endpoint of the unique geodesic `γ_v` starting at `p` with initial velocity
`v ∈ T_pM`. Alias of `Riemannian.Exponential.expMap`.

Blueprint: `def:exponential-map`. -/
abbrev expMap (g : Riemannian.RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : M :=
  Riemannian.Exponential.expMap (I := I) g p v

/-- **Math.** The maximal domain `O_p ⊆ T_pM` of `expMap g p`: the set of
initial velocities `v` for which the maximal geodesic `γ_v` is defined up to
time `1`. Alias of `Riemannian.Exponential.expDomain`.

Blueprint: `def:exponential-map`. -/
abbrev expDomain (g : Riemannian.RiemannianMetric I M) (p : M) :
    Set (TangentSpace I p) :=
  Riemannian.Exponential.expDomain (I := I) g p

end MorganTianLib

end
