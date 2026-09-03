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
set-relativised equation predicate.  It does not itself encode the curve
regularity in the prose definition; `IsGeodesicCurve` and
`IsGeodesicCurveOn` add continuity, and the regularity lemmas below expose
the further chart hypotheses needed for smoothness.  `IsGeodesic g γ` is
the special case `s = Set.univ`.

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
records only the geodesic equation. Pair it with `IsGeodesicCurveOn` below for
the source-faithful continuous curve predicate.  Smoothness is supplied by the
regularity lemmas in `GeodesicRegularity` under their stated chart hypotheses.

Blueprint: `def:geodesic`. -/
abbrev IsGeodesicOn (g : Riemannian.RiemannianMetric I M) (γ : ℝ → M)
    (s : Set ℝ) : Prop :=
  Riemannian.Geodesic.IsGeodesicOn (I := I) g γ s

/-- **Math.** A **continuous geodesic curve** on `s ⊆ ℝ`: the public
correspondence for Morgan--Tian's "smooth curve `γ` satisfying
`∇_{γ̇}γ̇ = 0`".  This is the DoCarmo predicate
`ContinuousOn γ s ∧ IsGeodesicOn g γ s`; use its second projection when only
the equation is needed.

Blueprint: `def:geodesic`. -/
abbrev IsGeodesicCurveOn (g : Riemannian.RiemannianMetric I M) (γ : ℝ → M)
    (s : Set ℝ) : Prop :=
  Riemannian.Geodesic.IsGeodesicCurveOn (I := I) g γ s

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

/-- **Math.** The zero tangent vector belongs to the maximal exponential
domain.  This local facade exposes the imported stationary-geodesic theorem
to the Morgan--Tian graph. -/
theorem zero_mem_expDomain (g : Riemannian.RiemannianMetric I M) (p : M) :
    (0 : TangentSpace I p) ∈ expDomain (I := I) g p :=
  Riemannian.Exponential.zero_mem_expDomain (I := I) g p

/-- **Math.** The maximal exponential domain is nonempty (it contains zero).
This is the corresponding local facade for the imported theorem. -/
theorem expDomain_nonempty (g : Riemannian.RiemannianMetric I M) (p : M) :
    (expDomain (I := I) g p).Nonempty :=
  Riemannian.Exponential.expDomain_nonempty (I := I) g p

end MorganTianLib

end
