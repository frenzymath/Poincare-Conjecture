import DoCarmoLib.Riemannian.Geodesic.InitialVelocity

/-!
# Continuity of the canonical maximal geodesic on its interval

`MaximalInterval.lean` defines `maximalGeodesic g p v : ℝ → M` (junk-extended
outside `maximalGeodesicInterval g p v`) and proves
`isGeodesicOnWithInitial_continuousOn`: an initial-data geodesic is continuous on
its interval, **without any completeness assumption**. The present file upgrades
that to the canonical curve: under the standard chart-validity clause
(`hsrc`, matching the hypothesis of `maximalGeodesic_eq_witness`), the canonical
`maximalGeodesic g p v` is continuous **on its maximal interval**.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space (TangentBundle I M)]

/-- **Math.** The canonical maximal geodesic is continuous on its maximal interval of
definition, under the chart-validity clause that every witness with initial data
`(p, v)` keeps its foot in the chart at `p`.

This is the local-geodesic analogue of `continuous_globalGeodesic` (which needs
`[CompleteSpace M]`): the canonical `maximalGeodesic` is continuous on
`maximalGeodesicInterval` **without** any completeness assumption. We obtain it by
gluing the continuity of a chosen local witness (via
`isGeodesicOnWithInitial_continuousOn`) with the uniqueness statement
`maximalGeodesic_eq_witness`, which identifies the canonical curve with any such
witness on the witness's interval. -/
theorem continuousOn_maximalGeodesic
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p}
    (hsrc : ∀ (γ' : ℝ → M) (J' : Set ℝ),
      IsGeodesicOnWithInitial (I := I) g γ' J' p v →
        ∀ s ∈ J', γ' s ∈ (chartAt H p).source) :
    ContinuousOn (maximalGeodesic (I := I) g p v) (maximalGeodesicInterval (I := I) g p v) := by
  intro t ht
  have hwit : MaximalGeodesicWitness (I := I) g p v t :=
    (mem_maximalGeodesicInterval_iff (I := I) (g := g) (p := p) (v := v)).mp ht
  obtain ⟨J, hJo, hJc, h0, htJ, hγ⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p v hwit
  -- Every point of `J` lies in the maximal interval (the same witness covers it).
  have hJ_sub : J ⊆ maximalGeodesicInterval (I := I) g p v := by
    intro s hs
    exact ⟨maximalGeodesicChosenCurve (I := I) g p v hwit, J, hJo, hJc, h0, hs, hγ⟩
  -- On `J`, the canonical maximal geodesic coincides with the chosen witness.
  have heq : ∀ s ∈ J, maximalGeodesic (I := I) g p v s =
      maximalGeodesicChosenCurve (I := I) g p v hwit s := by
    intro s hs
    exact maximalGeodesic_eq_witness (I := I) (g := g) (p := p) (v := v) hsrc hγ hJo hJc h0 hs
  -- The chosen witness is continuous on `J` (no completeness needed).
  have hcont : ContinuousOn (maximalGeodesicChosenCurve (I := I) g p v hwit) J :=
    isGeodesicOnWithInitial_continuousOn (I := I) (g := g) hγ
  -- The canonical maximal geodesic is therefore continuous on `J`.
  have hcontMax : ContinuousOn (maximalGeodesic (I := I) g p v) J := by
    exact hcont.congr (fun s hs => heq s hs)
  -- `J` is an open neighbourhood of `t`, so we get continuity at `t`.
  have hcontAt : ContinuousAt (maximalGeodesic (I := I) g p v) t :=
    hcontMax.continuousAt (hJo.mem_nhds htJ)
  exact hcontAt.continuousWithinAt

end Geodesic
end Riemannian

end
