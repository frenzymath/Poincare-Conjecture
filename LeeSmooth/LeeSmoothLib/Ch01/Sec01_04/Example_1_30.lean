import Mathlib
import LeeSmoothLib.Ch01.Sec01.Example_1_3
-- Declarations for this item will be appended below by the statement pipeline.

open ChartedSpace
open scoped ContDiff Manifold

noncomputable section

-- Semantic search note: no `lean_leansearch` tool was available in this environment, so the
-- chart choice was checked against `Example_1_3`, mathlib's `singletonChartedSpace` /
-- `isManifold_singleton` API, and `ChartedSpace.empty` for the empty-graph case.

/-- A nonempty bundled open set gives a nonempty subtype. -/
@[implicit_reducible] def opens_nonempty_of_nonempty_set {X : Type*} [TopologicalSpace X]
    (U : TopologicalSpace.Opens X)
    (hU : (U : Set X).Nonempty) : Nonempty U :=
  let ⟨x, hx⟩ := hU
  ⟨⟨x, hx⟩⟩

/-- A point on the graph determines that the domain open set is nonempty. -/
def graphOn_domain_nonempty {n k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k)}
    (p : U.graphOn f) : U.Nonempty :=
  ⟨p.1.1, (Set.mem_graphOn.1 p.2).1⟩

/-- If the domain set is empty, then the graph over it is empty. -/
theorem graphOn_isEmpty_of_not_nonempty {n k : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k))
    (hU : ¬ U.Nonempty) :
    IsEmpty (U.graphOn f) := by
  -- Any graph point would project to a point of `U`, contradicting the hypothesis.
  refine ⟨fun p ↦ hU (graphOn_domain_nonempty p)⟩

/-- The graph coordinate chart of a smooth function on a nonempty open subset of `ℝ^n`, obtained
by composing the homeomorphism from Example 1.3 with the inclusion of the open set into `ℝ^n`. -/
def graph_coordinate_chart {n k : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k))
    (hf : ContDiffOn ℝ ∞ f U) (hU_nonempty : U.Nonempty) :
    OpenPartialHomeomorph (U.graphOn f) (EuclideanSpace ℝ (Fin n)) :=
  let Uo : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨U, hU⟩
  (graph_coordinates U f hf.continuousOn).toOpenPartialHomeomorph ≫ₕ
    Uo.openPartialHomeomorphSubtypeCoe (opens_nonempty_of_nonempty_set Uo hU_nonempty)

/-- The graph coordinate chart is defined on all of the graph of `f`. -/
theorem graph_coordinate_chart_source {n k : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k))
    (hf : ContDiffOn ℝ ∞ f U) (hU_nonempty : U.Nonempty) :
    (graph_coordinate_chart U hU f hf hU_nonempty).source = Set.univ := by
  -- Both factors in the composite chart are defined everywhere on their natural domains.
  change Set.univ ∩ Set.univ = (Set.univ : Set (U.graphOn f))
  simp

/-- The target of the graph coordinate chart is exactly the open set `U`. -/
theorem graph_coordinate_chart_target {n k : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k))
    (hf : ContDiffOn ℝ ∞ f U) (hU_nonempty : U.Nonempty) :
    (graph_coordinate_chart U hU f hf hU_nonempty).target = U := by
  let Uo : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨U, hU⟩
  -- The final subtype inclusion is the only target restriction in the composite chart.
  rw [graph_coordinate_chart, OpenPartialHomeomorph.trans_target]
  ext x
  simp [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]

/-- The graph coordinate chart is the restriction of the first projection from the graph to the
domain open set. -/
theorem graph_coordinate_chart_apply {n k : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k))
    (hf : ContDiffOn ℝ ∞ f U) (hU_nonempty : U.Nonempty) (p : U.graphOn f) :
    graph_coordinate_chart U hU f hf hU_nonempty p = p.1.1 := by
  -- Composing with the subtype inclusion only forgets the proof that the first coordinate lies in
  -- `U`, so the chart is still the first projection.
  rw [graph_coordinate_chart, OpenPartialHomeomorph.trans_apply]
  simpa using graph_coordinates_apply U f hf.continuousOn p

/-- The graph of a smooth map `f : U → ℝ^k` on an open subset `U ⊆ ℝ^n` carries the canonical
charted-space structure determined by the graph coordinate chart when `U` is nonempty, and the
vacuous empty charted-space structure when `U` is empty. -/
@[implicit_reducible] def graph_charted_space {n k : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k))
    (hf : ContDiffOn ℝ ∞ f U) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (U.graphOn f) :=
  let _ : Decidable U.Nonempty := Classical.dec _
  if hU_nonempty : U.Nonempty then
    (graph_coordinate_chart U hU f hf hU_nonempty).singletonChartedSpace
      (graph_coordinate_chart_source U hU f hf hU_nonempty)
  else
    let _ : IsEmpty (U.graphOn f) := graphOn_isEmpty_of_not_nonempty U f hU_nonempty
    ChartedSpace.empty _ (U.graphOn f)

/-- In the charted-space structure on the graph of `f`, the chart at every point is the graph
coordinate chart. -/
theorem graph_charted_space_chartAt_eq {n k : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k))
    (hf : ContDiffOn ℝ ∞ f U) (p : U.graphOn f) :
    @chartAt (EuclideanSpace ℝ (Fin n)) _ (U.graphOn f) _
      (graph_charted_space U hU f hf) p =
      graph_coordinate_chart U hU f hf (graphOn_domain_nonempty p) := by
  by_cases hU_nonempty : U.Nonempty
  · -- In the nonempty case, `graph_charted_space` reduces to the singleton atlas generated by the
    -- graph chart.
    rw [graph_charted_space, dif_pos hU_nonempty]
    have hwitness :
        graph_coordinate_chart U hU f hf hU_nonempty =
          graph_coordinate_chart U hU f hf (graphOn_domain_nonempty p) := by
      cases Subsingleton.elim hU_nonempty (graphOn_domain_nonempty p)
      rfl
    calc
      @chartAt (EuclideanSpace ℝ (Fin n)) _ (U.graphOn f) _
          ((graph_coordinate_chart U hU f hf hU_nonempty).singletonChartedSpace
            (graph_coordinate_chart_source U hU f hf hU_nonempty)) p
          = graph_coordinate_chart U hU f hf hU_nonempty := by
              exact
                (graph_coordinate_chart U hU f hf hU_nonempty).singletonChartedSpace_chartAt_eq
                  (graph_coordinate_chart_source U hU f hf hU_nonempty)
      _ = graph_coordinate_chart U hU f hf (graphOn_domain_nonempty p) := hwitness
  · -- The empty branch is impossible because `p` already produces a point of `U`.
    exact (hU_nonempty (graphOn_domain_nonempty p)).elim

/-- Example 1.30: if `U ⊆ ℝ^n` is open and `f : U → ℝ^k` is smooth, then the graph of `f`
inherits the canonical smooth manifold structure modeled on `ℝ^n` from its graph coordinate
chart. -/
instance graph_charted_space_isManifold {n k : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k))
    (hf : ContDiffOn ℝ ∞ f U) :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin n)) _ _
      (EuclideanSpace ℝ (Fin n)) _ (𝓡 n) ∞ (U.graphOn f) _
      (graph_charted_space U hU f hf) := by
  by_cases hU_nonempty : U.Nonempty
  · -- When `U` is nonempty, the graph chart gives a singleton atlas with full source.
    rw [graph_charted_space, dif_pos hU_nonempty]
    exact
      (graph_coordinate_chart U hU f hf hU_nonempty).isManifold_singleton
        (I := 𝓡 n) (n := ∞)
        (graph_coordinate_chart_source U hU f hf hU_nonempty)
  · -- When `U` is empty, the graph is empty, so the vacuous charted-space structure is manifold.
    let _ : IsEmpty (U.graphOn f) := graphOn_isEmpty_of_not_nonempty U f hU_nonempty
    rw [graph_charted_space, dif_neg hU_nonempty]
    infer_instance

/-- A reformulation of Example 1.30 as an `IsManifold` proposition after installing
`graph_charted_space U hU f hf` as the charted-space structure on `U.graphOn f`. -/
theorem graph_smooth_structure {n k : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k))
    (hf : ContDiffOn ℝ ∞ f U) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (U.graphOn f) := graph_charted_space U hU f hf
    IsManifold (𝓡 n) ∞ (U.graphOn f) := by
  -- The charted-space structure from `graph_charted_space` is smooth by the singleton-atlas
  -- manifold instance proved above.
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (U.graphOn f) := graph_charted_space U hU f hf
  infer_instance

end
