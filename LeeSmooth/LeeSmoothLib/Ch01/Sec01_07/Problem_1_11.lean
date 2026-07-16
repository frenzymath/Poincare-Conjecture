import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import LeeSmoothLib.Ch02.Sec02_12.Problem_2_4
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

-- Semantic search tooling was unavailable in this environment; this file reuses the explicit
-- closed-ball atlas and smooth structure already constructed later in the project in Problem 2-4,
-- together with mathlib's standard manifold interior/boundary API.

section

local notation "ClosedUnitBall" n =>
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

local notation "OpenUnitBall" n =>
  Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1

local notation "UnitSphere" n =>
  Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- For Problem 1-11 (1), the closed unit ball in `ℝ^n` carries a topological
manifold-with-boundary structure. -/
noncomputable instance closed_unit_ball_topologicalManifoldWithBoundary (n : ℕ) :
    TopologicalManifoldWithBoundary n (ClosedUnitBall n) := by
  cases n with
  | zero =>
      exact closed_unit_ball_zero_topologicalManifoldWithBoundary
  | succ m =>
      cases m with
      | zero =>
          exact closed_unit_ball_one_smoothManifoldWithBoundary.toTopologicalManifoldWithBoundary
      | succ k =>
          let h := closed_unit_ball_higher_dimensional_smoothManifoldWithBoundary k
          exact h.toTopologicalManifoldWithBoundary

/-- Helper for Problem 1-11: in Lee's higher-dimensional boundary chart, a sphere point lands on
the boundary hyperplane of the half-space model. -/
lemma boundaryChartImage_mem_frontier_of_mem_sphere {k : ℕ}
    {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1}
    (i : Fin (k + 2)) (s : Bool)
    (hxSource : x ∈ (closed_unit_ball_boundary_chart k i s).source)
    (hxSphere : x.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :
    ((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2)) x) ∈
      frontier (Set.range (𝓡∂ (k + 2))) := by
  let _ : NeZero (k + 2) := ⟨Nat.succ_ne_zero _⟩
  let ui := split_at_coordinate i x.1
  have hx0 : 0 < closed_unit_ball_boundary_sign s * x.1 i := by
    -- Source membership is exactly the signed-coordinate positivity condition of the chart.
    simpa [closed_unit_ball_boundary_chart] using hxSource
  have hnorm : ‖x.1‖ = 1 := by
    -- A sphere point has ambient norm exactly `1`.
    simpa [Metric.mem_sphere, dist_eq_norm] using hxSphere
  have hnorm_sq : ‖x.1‖ ^ 2 = 1 := by
    nlinarith [hnorm]
  have hsplit :
      ‖x.1‖ ^ 2 = ‖ui.1‖ ^ 2 + ui.2 ^ 2 := by
    -- Splitting off the chart coordinate isolates the distinguished coordinate square.
    simpa [ui] using split_at_coordinate_symm_norm_sq i (split_at_coordinate i x.1)
  have hsnd_sq : ui.2 ^ 2 = 1 - ‖ui.1‖ ^ 2 := by
    linarith
  have hrad_nonneg : 0 ≤ 1 - ‖ui.1‖ ^ 2 := by
    nlinarith [sq_nonneg ui.2]
  have habs_sq :
      |ui.2| ^ 2 = (Real.sqrt (1 - ‖ui.1‖ ^ 2)) ^ 2 := by
    rw [sq_abs, Real.sq_sqrt hrad_nonneg]
    exact hsnd_sq
  have habs : |ui.2| = Real.sqrt (1 - ‖ui.1‖ ^ 2) := by
    -- Equality of the squared lengths upgrades to equality because both sides are nonnegative.
    nlinarith [habs_sq, abs_nonneg ui.2, Real.sqrt_nonneg (1 - ‖ui.1‖ ^ 2)]
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  change 0 = (((𝓡∂ (k + 2)) ((closed_unit_ball_boundary_chart k i s) x)) : EuclideanSpace ℝ
    (Fin (k + 2))) 0
  rw [closed_unit_ball_boundary_chart_apply_of_mem_source (k := k) i s hxSource]
  have hcoord :
      (((𝓡∂ (k + 2))
        (closed_unit_ball_boundary_chart_forward k i s x
          (closed_unit_ball_boundary_chart_source_pos i s
            (by simpa [closed_unit_ball_boundary_chart] using hxSource))) :
        EuclideanSpace ℝ (Fin (k + 2))) 0) =
        closed_unit_ball_boundary_sign s *
          (closed_unit_ball_boundary_branch k s ui.1 - ui.2) := by
    -- The `0`-th target coordinate is the normalized signed graph-distance coordinate.
    calc
      (((𝓡∂ (k + 2))
        (closed_unit_ball_boundary_chart_forward k i s x
          (closed_unit_ball_boundary_chart_source_pos i s
            (by simpa [closed_unit_ball_boundary_chart] using hxSource))) :
        EuclideanSpace ℝ (Fin (k + 2))) 0)
          = (closed_unit_ball_boundary_chart_forward_extend k i s x.1) 0 := by
              simp [modelWithCornersEuclideanHalfSpace, closed_unit_ball_boundary_chart_forward]
      _ = (split_at_coordinate (0 : Fin (k + 2))
            (closed_unit_ball_boundary_chart_forward_extend k i s x.1)).2 := by
              rw [split_at_coordinate_snd_apply]
      _ =
          closed_unit_ball_boundary_sign s *
            (closed_unit_ball_boundary_branch k s ui.1 - ui.2) := by
              simpa [ui] using congrArg Prod.snd
                (closed_unit_ball_boundary_chart_forward_extend_split (k := k) i s x.1)
  rw [hcoord]
  cases s with
  | false =>
      have hneg : ui.2 < 0 := by
        simpa [ui, split_at_coordinate_snd_apply, closed_unit_ball_boundary_sign] using hx0
      have hbranch : Real.sqrt (1 - ‖ui.1‖ ^ 2) = -ui.2 := by
        simpa [abs_of_neg hneg] using habs.symm
      simp [closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign, hbranch]
  | true =>
      have hpos : 0 < ui.2 := by
        simpa [ui, split_at_coordinate_snd_apply, closed_unit_ball_boundary_sign] using hx0
      have hbranch : Real.sqrt (1 - ‖ui.1‖ ^ 2) = ui.2 := by
        simpa [abs_of_nonneg hpos.le] using habs.symm
      simp [closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign, hbranch]

/-- Helper for Problem 1-11: Lee's center chart sends every point of the small interior patch to
the interior of the model half-space. -/
lemma centerChartImage_mem_interior {k : ℕ}
    {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1}
    (hxSource : x ∈ (closed_unit_ball_center_chart k).source) :
    ((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2)) x) ∈
      interior (Set.range (𝓡∂ (k + 2))) := by
  let _ : NeZero (k + 2) := ⟨Nat.succ_ne_zero _⟩
  have hcenter : ‖x.1‖ < (1 : ℝ) / 2 := by
    -- The center chart source is exactly Lee's radius-`1/2` interior patch.
    have hx' := hxSource
    rw [closed_unit_ball_center_chart, OpenPartialHomeomorph.trans_source] at hx'
    simpa [closed_unit_ball_center_chart_source] using hx'.1
  have hcoord : |x.1 0| < (1 : ℝ) / 2 := by
    -- Any coordinate is controlled by the ambient Euclidean norm.
    exact lt_of_le_of_lt (closed_unit_ball_coordinate_abs_le_norm x.1 0) hcenter
  have hlower : -((1 : ℝ) / 2) < x.1 0 := by
    exact (abs_lt.mp hcoord).1
  have hpos : 0 < x.1 0 + 1 := by
    linarith
  rw [interior_range_modelWithCornersEuclideanHalfSpace]
  -- The center chart is just translation by the fixed interior half-space basepoint.
  rw [closed_unit_ball_center_chart_extend_eq_add k hxSource]
  simpa [closed_unit_ball_center_target_point] using hpos

/-- Helper for Problem 1-11: in Lee's higher-dimensional boundary chart, an open-ball point lands
strictly inside the model half-space. -/
lemma boundaryChartImage_mem_interior_of_mem_ball {k : ℕ}
    {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1}
    (i : Fin (k + 2)) (s : Bool)
    (hxSource : x ∈ (closed_unit_ball_boundary_chart k i s).source)
    (hxBall : x.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :
    ((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2)) x) ∈
      interior (Set.range (𝓡∂ (k + 2))) := by
  let _ : NeZero (k + 2) := ⟨Nat.succ_ne_zero _⟩
  let ui := split_at_coordinate i x.1
  have hx0 : 0 < closed_unit_ball_boundary_sign s * x.1 i := by
    -- Source membership is exactly the signed-coordinate positivity condition of the chart.
    simpa [closed_unit_ball_boundary_chart] using hxSource
  have hnorm : ‖x.1‖ < 1 := by
    -- An interior point of the ambient ball has norm strictly smaller than `1`.
    simpa [Metric.mem_ball, dist_eq_norm] using hxBall
  have hnorm_sq : ‖x.1‖ ^ 2 < 1 := by
    nlinarith [hnorm, norm_nonneg x.1]
  have hsplit :
      ‖x.1‖ ^ 2 = ‖ui.1‖ ^ 2 + ui.2 ^ 2 := by
    -- Splitting off the chart coordinate isolates the distinguished coordinate square.
    simpa [ui] using split_at_coordinate_symm_norm_sq i (split_at_coordinate i x.1)
  have hsnd_sq_lt : ui.2 ^ 2 < 1 - ‖ui.1‖ ^ 2 := by
    linarith
  have hrad_nonneg : 0 ≤ 1 - ‖ui.1‖ ^ 2 := by
    nlinarith [sq_nonneg ui.2]
  have habs_sq_lt :
      |ui.2| ^ 2 < (Real.sqrt (1 - ‖ui.1‖ ^ 2)) ^ 2 := by
    rw [sq_abs, Real.sq_sqrt hrad_nonneg]
    exact hsnd_sq_lt
  have habs_lt : |ui.2| < Real.sqrt (1 - ‖ui.1‖ ^ 2) := by
    -- Strict inequality of squares upgrades to strict inequality because both sides are
    -- nonnegative.
    nlinarith [habs_sq_lt, abs_nonneg ui.2, Real.sqrt_nonneg (1 - ‖ui.1‖ ^ 2)]
  rw [interior_range_modelWithCornersEuclideanHalfSpace]
  change 0 < (((𝓡∂ (k + 2)) ((closed_unit_ball_boundary_chart k i s) x)) : EuclideanSpace ℝ
    (Fin (k + 2))) 0
  rw [closed_unit_ball_boundary_chart_apply_of_mem_source (k := k) i s hxSource]
  have hcoord :
      (((𝓡∂ (k + 2))
        (closed_unit_ball_boundary_chart_forward k i s x
          (closed_unit_ball_boundary_chart_source_pos i s
            (by simpa [closed_unit_ball_boundary_chart] using hxSource))) :
        EuclideanSpace ℝ (Fin (k + 2))) 0) =
        closed_unit_ball_boundary_sign s *
          (closed_unit_ball_boundary_branch k s ui.1 - ui.2) := by
    -- The `0`-th target coordinate is the normalized signed graph-distance coordinate.
    calc
      (((𝓡∂ (k + 2))
        (closed_unit_ball_boundary_chart_forward k i s x
          (closed_unit_ball_boundary_chart_source_pos i s
            (by simpa [closed_unit_ball_boundary_chart] using hxSource))) :
        EuclideanSpace ℝ (Fin (k + 2))) 0)
          = (closed_unit_ball_boundary_chart_forward_extend k i s x.1) 0 := by
              simp [modelWithCornersEuclideanHalfSpace, closed_unit_ball_boundary_chart_forward]
      _ = (split_at_coordinate (0 : Fin (k + 2))
            (closed_unit_ball_boundary_chart_forward_extend k i s x.1)).2 := by
              rw [split_at_coordinate_snd_apply]
      _ = closed_unit_ball_boundary_sign s *
            (closed_unit_ball_boundary_branch k s ui.1 - ui.2) := by
              simpa [ui] using congrArg Prod.snd
                (closed_unit_ball_boundary_chart_forward_extend_split (k := k) i s x.1)
  rw [hcoord]
  cases s with
  | false =>
      have hneg : ui.2 < 0 := by
        simpa [ui, split_at_coordinate_snd_apply, closed_unit_ball_boundary_sign] using hx0
      have hgap : 0 < ui.2 + Real.sqrt (1 - ‖ui.1‖ ^ 2) := by
        have hstrict : -ui.2 < Real.sqrt (1 - ‖ui.1‖ ^ 2) := by
          simpa [abs_of_neg hneg] using habs_lt
        linarith
      simpa [closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign] using hgap
  | true =>
      have hpos : 0 < ui.2 := by
        simpa [ui, split_at_coordinate_snd_apply, closed_unit_ball_boundary_sign] using hx0
      have hgap : 0 < Real.sqrt (1 - ‖ui.1‖ ^ 2) - ui.2 := by
        have hstrict : ui.2 < Real.sqrt (1 - ‖ui.1‖ ^ 2) := by
          simpa [abs_of_nonneg hpos.le] using habs_lt
        linarith
      simpa [closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign] using hgap

/-- Problem 1-11 (2): every point of the boundary sphere `S^{n-1}` of the closed unit ball is a
boundary point for the manifold-with-boundary structure on the closed unit ball. -/
theorem closed_unit_ball_isBoundaryPoint_of_mem_sphere {n : ℕ} {x : ClosedUnitBall n}
    (hx : ((x : ClosedUnitBall n) : EuclideanSpace ℝ (Fin n)) ∈ UnitSphere n) :
    (leeBoundaryModelWithCorners n).IsBoundaryPoint x := by
  cases n with
  | zero =>
      have hnorm : ‖x.1‖ = 1 := by
        -- The sphere hypothesis is impossible in dimension zero because every vector is `0`.
        simpa [Metric.mem_sphere, dist_eq_norm] using hx
      have hzero : x.1 = 0 := by
        exact Subsingleton.elim _ _
      rw [hzero, norm_zero] at hnorm
      have hfalse : False := by
        have : (0 : ℝ) = 1 := by
          exact hnorm
        exact zero_ne_one this
      exact False.elim hfalse
  | succ m =>
      cases m with
      | zero =>
          letI : Fact ((-1 : ℝ) < 1) := closed_unit_ball_one_interval_fact
          letI : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
            closed_unit_ball_one_nonempty
          letI : ChartedSpace (Set.Icc (-1 : ℝ) 1)
              (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
            closed_unit_ball_one_chartedSpace_Icc
          letI : ChartedSpace (EuclideanHalfSpace 1)
              (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
            closed_unit_ball_one_chartedSpace_halfSpace
          let e : OpenPartialHomeomorph
              (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)
              (Set.Icc (-1 : ℝ) 1) :=
            chartAt (Set.Icc (-1 : ℝ) 1) x
          have hExt :
              extChartAt (𝓡∂ 1) x x =
                extChartAt (𝓡∂ 1) (closed_unit_ball_one_to_Icc x)
                  (closed_unit_ball_one_to_Icc x) := by
            -- The transported singleton chart factors `extChartAt` through the interval point.
            have hComp :
                (extChartAt (𝓡∂ 1) x) x =
                  ((e.toPartialEquiv ≫ extChartAt (𝓡∂ 1) (e x)) x) := by
              exact congrArg (fun e => e x)
                (extChartAt_comp (I := (𝓡∂ 1)) (H := EuclideanHalfSpace 1)
                  (H' := Set.Icc (-1 : ℝ) 1) (x := x))
            simpa [e, Topology.IsOpenEmbedding.singletonChartedSpace_chartAt_eq] using hComp
          have habs : |x.1 0| = 1 := by
            -- In `ℝ¹`, lying on the unit sphere means the unique coordinate has absolute value `1`.
            simpa [Metric.mem_sphere, dist_eq_norm, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
              using hx
          by_cases hnonneg : 0 ≤ x.1 0
          · have hcoord : x.1 0 = 1 := by
              have habs' : |x.1 0| = x.1 0 := abs_of_nonneg hnonneg
              linarith [habs, habs']
            let topIcc : Set.Icc (-1 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩
            have hIcc :
                closed_unit_ball_one_to_Icc x = topIcc := by
              apply Subtype.ext
              simp [closed_unit_ball_one_to_Icc, topIcc, hcoord]
            have hTop : (𝓡∂ 1).IsBoundaryPoint topIcc := by
              simpa [topIcc] using
                (Icc_isBoundaryPoint_top (x := (-1 : ℝ)) (y := (1 : ℝ)))
            have hSelf : (𝓡∂ 1).IsBoundaryPoint x := by
              rw [ModelWithCorners.IsBoundaryPoint, hExt]
              simpa [hIcc] using hTop
            simpa [leeBoundaryModelWithCorners] using hSelf
          · have hneg : x.1 0 < 0 := lt_of_not_ge hnonneg
            have hcoord : x.1 0 = -1 := by
              have habs' : |x.1 0| = -x.1 0 := abs_of_neg hneg
              linarith [habs, habs']
            let botIcc : Set.Icc (-1 : ℝ) 1 := ⟨-1, by constructor <;> norm_num⟩
            have hIcc :
                closed_unit_ball_one_to_Icc x = botIcc := by
              apply Subtype.ext
              simp [closed_unit_ball_one_to_Icc, botIcc, hcoord]
            have hBot : (𝓡∂ 1).IsBoundaryPoint botIcc := by
              simpa [botIcc] using
                (Icc_isBoundaryPoint_bot (x := (-1 : ℝ)) (y := (1 : ℝ)))
            have hSelf : (𝓡∂ 1).IsBoundaryPoint x := by
              rw [ModelWithCorners.IsBoundaryPoint, hExt]
              simpa [hIcc] using hBot
            simpa [leeBoundaryModelWithCorners] using hSelf
      | succ k =>
          have hnot : ¬ ‖x.1‖ < (1 : ℝ) / 2 := by
            -- A sphere point cannot lie in the radius-`1/2` center patch.
            have hnorm : ‖x.1‖ = 1 := by
              simpa [Metric.mem_sphere, dist_eq_norm] using hx
            linarith
          let is := (closed_unit_ball_boundary_choice_data k x hnot).1
          have hchart :
              chartAt (EuclideanHalfSpace (k + 2)) x =
                closed_unit_ball_boundary_chart k is.1 is.2 := by
            -- Outside the center patch, `chartAt` is exactly Lee's selected signed boundary chart.
            change closed_unit_ball_chartAtLocal k x =
              closed_unit_ball_boundary_chart k
                (closed_unit_ball_boundary_choice_data k x hnot).1.1
                (closed_unit_ball_boundary_choice_data k x hnot).1.2
            simpa using closed_unit_ball_chartAtLocal_of_not_norm_lt k x hnot
          have hxSource : x ∈ (closed_unit_ball_boundary_chart k is.1 is.2).source := by
            -- The selected boundary chart contains `x` by construction.
            have hxLocal : x ∈ (closed_unit_ball_chartAtLocal k x).source :=
              mem_closed_unit_ball_chartAtLocal_source k x
            rw [closed_unit_ball_chartAtLocal_of_not_norm_lt k x hnot] at hxLocal
            simpa [is] using hxLocal
          -- Route correction: use the selected chart directly instead of unfolding the whole atlas.
          change
            ((chartAt (EuclideanHalfSpace (k + 2)) x).extend
                (leeBoundaryModelWithCorners (k + 2)) x) ∈
              frontier (Set.range (leeBoundaryModelWithCorners (k + 2)))
          rw [hchart]
          exact boundaryChartImage_mem_frontier_of_mem_sphere is.1 is.2 hxSource hx

/-- For Problem 1-11 (3), every point of the open unit ball `B^n` is an interior point for the
manifold-with-boundary structure on the closed unit ball. -/
theorem closed_unit_ball_isInteriorPoint_of_mem_ball {n : ℕ} {x : ClosedUnitBall n}
    (hx : ((x : ClosedUnitBall n) : EuclideanSpace ℝ (Fin n)) ∈ OpenUnitBall n) :
    (leeBoundaryModelWithCorners n).IsInteriorPoint x := by
  cases n with
  | zero =>
      -- In dimension zero, the closed unit ball is boundaryless, so every point is interior.
      simpa [leeBoundaryModelWithCorners] using
        (show (𝓡 0).IsInteriorPoint x from BoundarylessManifold.isInteriorPoint)
  | succ m =>
      cases m with
      | zero =>
          letI : Fact ((-1 : ℝ) < 1) := closed_unit_ball_one_interval_fact
          letI : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
            closed_unit_ball_one_nonempty
          letI : ChartedSpace (Set.Icc (-1 : ℝ) 1)
              (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
            closed_unit_ball_one_chartedSpace_Icc
          letI : ChartedSpace (EuclideanHalfSpace 1)
              (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
            closed_unit_ball_one_chartedSpace_halfSpace
          let e : OpenPartialHomeomorph
              (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)
              (Set.Icc (-1 : ℝ) 1) :=
            chartAt (Set.Icc (-1 : ℝ) 1) x
          have hExt :
              extChartAt (𝓡∂ 1) x x =
                extChartAt (𝓡∂ 1) (closed_unit_ball_one_to_Icc x)
                  (closed_unit_ball_one_to_Icc x) := by
            -- The transported singleton chart factors `extChartAt` through the interval point.
            have hComp :
                (extChartAt (𝓡∂ 1) x) x =
                  ((e.toPartialEquiv ≫ extChartAt (𝓡∂ 1) (e x)) x) := by
              exact congrArg (fun e => e x)
                (extChartAt_comp (I := (𝓡∂ 1)) (H := EuclideanHalfSpace 1)
                  (H' := Set.Icc (-1 : ℝ) 1) (x := x))
            simpa [e, Topology.IsOpenEmbedding.singletonChartedSpace_chartAt_eq] using hComp
          have hcoord : -1 < x.1 0 ∧ x.1 0 < 1 := by
            have hnorm : ‖x.1‖ < 1 := by
              -- In `ℝ¹`, interior-ball membership is the same as strict coordinate inequality.
              simpa [Metric.mem_ball, dist_eq_norm] using hx
            have habs : |x.1 0| < 1 := by
              simpa [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs] using hnorm
            simpa using abs_lt.mp habs
          have hIcc : (𝓡∂ 1).IsInteriorPoint (closed_unit_ball_one_to_Icc x) := by
            simpa [closed_unit_ball_one_to_Icc] using
              (Icc_isInteriorPoint_interior
                (x := (-1 : ℝ)) (y := (1 : ℝ)) (p := closed_unit_ball_one_to_Icc x) hcoord)
          have hSelf : (𝓡∂ 1).IsInteriorPoint x := by
            rw [ModelWithCorners.IsInteriorPoint, hExt]
            exact hIcc
          simpa [leeBoundaryModelWithCorners] using hSelf
      | succ k =>
          by_cases hcenter : ‖x.1‖ < (1 : ℝ) / 2
          · have hchart :
                chartAt (EuclideanHalfSpace (k + 2)) x = closed_unit_ball_center_chart k := by
              -- Inside the center patch, `chartAt` is Lee's translation chart.
              change closed_unit_ball_chartAtLocal k x = closed_unit_ball_center_chart k
              exact closed_unit_ball_chartAtLocal_of_norm_lt k x hcenter
            have hxSource : x ∈ (closed_unit_ball_center_chart k).source := by
              -- The selected center chart contains `x` by construction.
              have hxLocal : x ∈ (closed_unit_ball_chartAtLocal k x).source :=
                mem_closed_unit_ball_chartAtLocal_source k x
              rw [closed_unit_ball_chartAtLocal_of_norm_lt k x hcenter] at hxLocal
              exact hxLocal
            change
              ((chartAt (EuclideanHalfSpace (k + 2)) x).extend
                  (leeBoundaryModelWithCorners (k + 2)) x) ∈
                interior (Set.range (leeBoundaryModelWithCorners (k + 2)))
            rw [hchart]
            exact centerChartImage_mem_interior hxSource
          · let is := (closed_unit_ball_boundary_choice_data k x hcenter).1
            have hchart :
                chartAt (EuclideanHalfSpace (k + 2)) x =
                  closed_unit_ball_boundary_chart k is.1 is.2 := by
              -- Outside the center patch, `chartAt` is the selected signed boundary chart.
              change closed_unit_ball_chartAtLocal k x =
                closed_unit_ball_boundary_chart k
                  (closed_unit_ball_boundary_choice_data k x hcenter).1.1
                  (closed_unit_ball_boundary_choice_data k x hcenter).1.2
              simpa using closed_unit_ball_chartAtLocal_of_not_norm_lt k x hcenter
            have hxSource : x ∈ (closed_unit_ball_boundary_chart k is.1 is.2).source := by
              -- The selected boundary chart contains `x` by construction.
              have hxLocal : x ∈ (closed_unit_ball_chartAtLocal k x).source :=
                mem_closed_unit_ball_chartAtLocal_source k x
              rw [closed_unit_ball_chartAtLocal_of_not_norm_lt k x hcenter] at hxLocal
              simpa [is] using hxLocal
            -- Route correction: use the selected chart directly instead of unfolding the whole
            -- atlas.
            change
              ((chartAt (EuclideanHalfSpace (k + 2)) x).extend
                  (leeBoundaryModelWithCorners (k + 2)) x) ∈
                interior (Set.range (leeBoundaryModelWithCorners (k + 2)))
            rw [hchart]
            exact boundaryChartImage_mem_interior_of_mem_ball is.1 is.2 hxSource hx

/-- For Problem 1-11 (4), the closed unit ball in `ℝ^n` carries the explicit smooth
manifold-with-boundary structure built from Lee's stereographic-boundary charts. -/
noncomputable instance closed_unit_ball_smoothManifoldWithBoundary (n : ℕ) :
    SmoothManifoldWithBoundary n (ClosedUnitBall n) := by
  cases n with
  | zero =>
      exact closed_unit_ball_zero_smoothManifoldWithBoundary
  | succ m =>
      cases m with
      | zero =>
          exact closed_unit_ball_one_smoothManifoldWithBoundary
      | succ k =>
          exact closed_unit_ball_higher_dimensional_smoothManifoldWithBoundary k

/-- For Problem 1-11 (5), for the chosen smooth structure on the closed unit ball, the subtype
inclusion into `ℝ^n` is smooth. This is the source-facing bridge formalizing that smooth interior
charts agree with the standard smooth structure on the open unit ball. -/
theorem closed_unit_ball_subtype_val_contMDiff (n : ℕ) :
    ContMDiff (leeBoundaryModelWithCorners n) (𝓡 n) ∞
      (Subtype.val :
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 →
          EuclideanSpace ℝ (Fin n)) := by
  cases n with
  | zero =>
      -- The imported zero-dimensional model already proves smoothness of the subtype inclusion.
      simpa using closed_unit_ball_zero_inclusion_contMDiff
  | succ m =>
      cases m with
      | zero =>
          -- In dimension one, the transported interval model gives the desired smooth inclusion.
          simpa using closed_unit_ball_one_inclusion_contMDiff
      | succ k =>
          -- In higher dimensions, reuse the previously constructed stereographic atlas proof.
          simpa using closed_unit_ball_higher_dimensional_inclusion_contMDiff k

end
