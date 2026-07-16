import LeeSmoothLib.Ch01.Sec01.Lemma_1_10
import LeeSmoothLib.Ch01.Sec01_05.Definition_1_5_extra_1
import Mathlib.Topology.Subpath
import Mathlib.Topology.UnitInterval

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [TopologicalManifoldWithBoundary n M]

/-- Helper for Proposition 1.40: positive-dimensional Euclidean half-space carries the inherited
pseudo-metric structure from its ambient Euclidean space. -/
local instance euclideanHalfSpacePseudoMetricSpace (k : ℕ) [NeZero k] :
    PseudoMetricSpace (EuclideanHalfSpace k) := by
  change PseudoMetricSpace { x : EuclideanSpace ℝ (Fin k) // 0 ≤ x 0 }
  infer_instance

/-- A coordinate ball in Lee's boundary model is the source of a chart whose target is an open
metric ball centered away from the boundary hyperplane. In dimension `0`, this is the ordinary
coordinate-ball condition in `ℝ^0`. -/
def IsBoundaryModelCoordinateBall (n : ℕ) (s : Set M) : Prop :=
  match n with
  | 0 =>
      ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 0)),
        e.source = s ∧
          ∃ c : EuclideanSpace ℝ (Fin 0), ∃ r : ℝ, 0 < r ∧ e.target = Metric.ball c r
  | m + 1 =>
      let _ : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
      show Prop from
        ∃ e : OpenPartialHomeomorph M { x : EuclideanSpace ℝ (Fin (m + 1)) // 0 ≤ x 0 },
          e.source = s ∧
            ∃ c : { x : EuclideanSpace ℝ (Fin (m + 1)) // 0 ≤ x 0 }, ∃ r : ℝ,
              0 < r ∧ r < c.1 0 ∧ e.target = Metric.ball c r

/-- A coordinate half-ball in Lee's boundary model is the source of a chart whose target is an open
metric ball centered on the boundary hyperplane. In dimension `0` there are no half-balls. -/
def IsBoundaryModelCoordinateHalfBall (n : ℕ) (s : Set M) : Prop :=
  match n with
  | 0 => False
  | m + 1 =>
      let _ : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
      show Prop from
        ∃ e : OpenPartialHomeomorph M { x : EuclideanSpace ℝ (Fin (m + 1)) // 0 ≤ x 0 },
          e.source = s ∧
            ∃ c : { x : EuclideanSpace ℝ (Fin (m + 1)) // 0 ≤ x 0 }, ∃ r : ℝ,
              0 < r ∧ c.1 0 = 0 ∧ e.target = Metric.ball c r

/-- A precompact boundary-model coordinate ball is a coordinate ball with compact closure. -/
def IsPrecompactBoundaryModelCoordinateBall (n : ℕ) (s : Set M) : Prop :=
  IsBoundaryModelCoordinateBall n s ∧ IsCompact (closure s)

/-- A precompact boundary-model coordinate half-ball is a coordinate half-ball with compact
closure. -/
def IsPrecompactBoundaryModelCoordinateHalfBall (n : ℕ) (s : Set M) : Prop :=
  IsBoundaryModelCoordinateHalfBall n s ∧ IsCompact (closure s)

/-- A basis all of whose members are precompact boundary-model coordinate balls or half-balls. -/
class IsPrecompactBoundaryModelCoordinateBallHalfBallBasis
    (n : ℕ) (b : Set (Set M)) : Prop where
  isTopologicalBasis : TopologicalSpace.IsTopologicalBasis b
  mem_isPrecompactBoundaryModelCoordinateBall_or_halfBall :
    ∀ s ∈ b,
      IsPrecompactBoundaryModelCoordinateBall n s ∨
        IsPrecompactBoundaryModelCoordinateHalfBall n s

/-- Helper for Proposition 1.40: in dimension `0`, a precompact coordinate ball is already a
precompact boundary-model coordinate ball because the boundary model is `ℝ^0`. -/
theorem isPrecompactBoundaryModelCoordinateBall_of_isPrecompactCoordinateBall_zero
    {s : Set M} [TopologicalManifoldWithBoundary 0 M] (hs : IsPrecompactCoordinateBall 0 s) :
    IsPrecompactBoundaryModelCoordinateBall 0 s := by
  -- Unpack the ordinary coordinate-ball witness and reuse the same chart in the boundary model.
  rcases hs with ⟨⟨e, hs, he⟩, hcompact⟩
  rcases he with ⟨c, r, hr, htarget⟩
  exact ⟨⟨e, hs, c, r, hr, htarget⟩, hcompact⟩

/-- Helper for Proposition 1.40: restricting a boundary chart to an interior Euclidean ball with
compactly contained closed ball produces a precompact boundary-model coordinate ball. -/
theorem isPrecompactBoundaryModelCoordinateBall_chartPreimageMetricBall
    {m : ℕ} [T2Space M] (e : OpenPartialHomeomorph M (EuclideanHalfSpace (m + 1)))
    {c : EuclideanHalfSpace (m + 1)} {r : ℝ} (hr : 0 < r) (hc : r < c.1 0)
    (hclosed : Metric.closedBall c r ⊆ e.target) :
    IsPrecompactBoundaryModelCoordinateBall (m + 1) (e.symm '' Metric.ball c r) := by
  let e' := e.trans (OpenPartialHomeomorph.ofSet (Metric.ball c r) Metric.isOpen_ball)
  have hball_target : Metric.ball c r ⊆ e.target := by
    exact (Metric.ball_subset_closedBall : Metric.ball c r ⊆ Metric.closedBall c r).trans hclosed
  have hsource : e'.source = e.symm '' Metric.ball c r := by
    -- The restricted chart is defined exactly on the inverse image of the chosen Euclidean ball.
    dsimp [e']
    exact (e.symm_image_eq_source_inter_preimage hball_target).symm
  have htarget : e'.target = Metric.ball c r := by
    -- On the target side, the restriction keeps precisely the chosen Euclidean ball.
    dsimp [e']
    exact inter_eq_left.2 hball_target
  have hcompactCarrier : IsCompact (e.symm '' Metric.closedBall c r) := by
    -- Compactness of the half-space closed ball comes from the ambient Euclidean closed ball.
    have hcoord :
        Continuous fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0 := by
      exact PiLp.continuous_apply (p := (2 : ℕ∞)) (β := fun _ : Fin (m + 1) => ℝ)
        (i := (0 : Fin (m + 1)))
    have hclosedHalf :
        IsClosed { x : EuclideanSpace ℝ (Fin (m + 1)) | 0 ≤ x 0 } := by
      exact isClosed_le continuous_const hcoord
    have hcompactBall : IsCompact (Metric.closedBall c r : Set (EuclideanHalfSpace (m + 1))) := by
      have hambient : IsCompact (Metric.closedBall c.1 r) :=
        isCompact_closedBall (x := c.1) (r := r)
      simpa [Metric.closedBall, Subtype.dist_eq] using
        hclosedHalf.isClosedEmbedding_subtypeVal.isCompact_preimage hambient
    exact hcompactBall.image_of_continuousOn
      (e.continuousOn_symm.mono hclosed)
  have hclosureCompact : IsCompact (closure (e.symm '' Metric.ball c r)) := by
    -- The closure stays inside the compact pullback of the closed Euclidean ball.
    exact hcompactCarrier.closure_of_subset
      (Set.image_mono (Metric.ball_subset_closedBall : Metric.ball c r ⊆ Metric.closedBall c r))
  refine ⟨?_, hclosureCompact⟩
  exact ⟨e', hsource, c, r, hr, hc, htarget⟩

/-- Helper for Proposition 1.40: restricting a boundary chart to a Euclidean ball centered on the
boundary hyperplane produces a precompact boundary-model coordinate half-ball. -/
theorem isPrecompactBoundaryModelCoordinateHalfBall_chartPreimageMetricBall
    {m : ℕ} [T2Space M] (e : OpenPartialHomeomorph M (EuclideanHalfSpace (m + 1)))
    {c : EuclideanHalfSpace (m + 1)} {r : ℝ} (hr : 0 < r) (hc : c.1 0 = 0)
    (hclosed : Metric.closedBall c r ⊆ e.target) :
    IsPrecompactBoundaryModelCoordinateHalfBall (m + 1) (e.symm '' Metric.ball c r) := by
  let e' := e.trans (OpenPartialHomeomorph.ofSet (Metric.ball c r) Metric.isOpen_ball)
  have hball_target : Metric.ball c r ⊆ e.target := by
    exact (Metric.ball_subset_closedBall : Metric.ball c r ⊆ Metric.closedBall c r).trans hclosed
  have hsource : e'.source = e.symm '' Metric.ball c r := by
    -- The restricted chart is defined exactly on the inverse image of the chosen Euclidean ball.
    dsimp [e']
    exact (e.symm_image_eq_source_inter_preimage hball_target).symm
  have htarget : e'.target = Metric.ball c r := by
    -- On the target side, the restriction keeps precisely the chosen Euclidean ball.
    dsimp [e']
    exact inter_eq_left.2 hball_target
  have hcompactCarrier : IsCompact (e.symm '' Metric.closedBall c r) := by
    -- Compactness of the half-space closed ball comes from the ambient Euclidean closed ball.
    have hcoord :
        Continuous fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0 := by
      exact PiLp.continuous_apply (p := (2 : ℕ∞)) (β := fun _ : Fin (m + 1) => ℝ)
        (i := (0 : Fin (m + 1)))
    have hclosedHalf :
        IsClosed { x : EuclideanSpace ℝ (Fin (m + 1)) | 0 ≤ x 0 } := by
      exact isClosed_le continuous_const hcoord
    have hcompactBall : IsCompact (Metric.closedBall c r : Set (EuclideanHalfSpace (m + 1))) := by
      have hambient : IsCompact (Metric.closedBall c.1 r) :=
        isCompact_closedBall (x := c.1) (r := r)
      simpa [Metric.closedBall, Subtype.dist_eq] using
        hclosedHalf.isClosedEmbedding_subtypeVal.isCompact_preimage hambient
    exact hcompactBall.image_of_continuousOn
      (e.continuousOn_symm.mono hclosed)
  have hclosureCompact : IsCompact (closure (e.symm '' Metric.ball c r)) := by
    -- The closure stays inside the compact pullback of the closed Euclidean ball.
    exact hcompactCarrier.closure_of_subset
      (Set.image_mono (Metric.ball_subset_closedBall : Metric.ball c r ⊆ Metric.closedBall c r))
  refine ⟨?_, hclosureCompact⟩
  exact ⟨e', hsource, c, r, hr, hc, htarget⟩

/-- Helper for Proposition 1.40: in positive dimension, every open neighborhood contains a
precompact boundary-model coordinate ball or half-ball. -/
theorem exists_precompactBoundaryModelCoordinateBallOrHalfBall_subset_of_mem_open_succ
    {m : ℕ} [TopologicalManifoldWithBoundary (m + 1) M] {x : M} {u : Set M}
    (hx : x ∈ u) (hu : IsOpen u) :
    ∃ s : Set M,
      (IsPrecompactBoundaryModelCoordinateBall (m + 1) s ∨
        IsPrecompactBoundaryModelCoordinateHalfBall (m + 1) s) ∧
      x ∈ s ∧ s ⊆ u := by
  let e := chartAt (EuclideanHalfSpace (m + 1)) x
  let y : EuclideanHalfSpace (m + 1) := e x
  let w : Set (EuclideanHalfSpace (m + 1)) := e '' (e.source ∩ u)
  have hxsource : x ∈ e.source := mem_chart_source _ x
  have hyw : y ∈ w := by
    exact ⟨x, ⟨hxsource, hx⟩, rfl⟩
  have hw_open : IsOpen w := by
    -- The chart image of the open neighborhood inside the chart source is open in the model.
    simpa [w] using e.isOpen_image_source_inter hu
  obtain ⟨r, hr, hclosed⟩ : ∃ r : ℝ, 0 < r ∧ Metric.closedBall y r ⊆ w := by
    -- Choose a small closed model ball around the charted point inside that open image.
    exact Metric.nhds_basis_closedBall.mem_iff.1 (hw_open.mem_nhds hyw)
  have hw_target : w ⊆ e.target := by
    -- Any chart image of a subset of the source lands in the chart target.
    simpa [w] using (Set.image_mono (show e.source ∩ u ⊆ e.source from inter_subset_left)).trans
      e.image_source_eq_target.subset
  have hs_subset_u {ρ : ℝ} (hρw : Metric.ball y ρ ⊆ w) : e.symm '' Metric.ball y ρ ⊆ u := by
    have hs_subset_source_u : e.symm '' Metric.ball y ρ ⊆ e.source ∩ u := by
      -- Pulling back a subset of the chosen chart image recovers the original neighborhood piece.
      change e.symm '' Metric.ball y ρ ⊆ e.source ∩ u
      refine (Set.image_mono hρw).trans ?_
      have himage : e.symm '' w = e.source ∩ u := by
        simpa [w] using e.symm_image_image_of_subset_source
          (s := e.source ∩ u) (show e.source ∩ u ⊆ e.source from inter_subset_left)
      exact himage.subset
    exact fun z hz ↦ (hs_subset_source_u hz).2
  by_cases hy_boundary : y.1 0 = 0
  · let s : Set M := e.symm '' Metric.ball y r
    have hs_precompact : IsPrecompactBoundaryModelCoordinateHalfBall (m + 1) s := by
      -- A chart ball centered on the boundary hyperplane is a coordinate half-ball.
      simpa [s, y] using isPrecompactBoundaryModelCoordinateHalfBall_chartPreimageMetricBall
        (M := M) (m := m) e hr hy_boundary (hclosed.trans hw_target)
    have hxs : x ∈ s := by
      -- The chart center lies in every positive-radius ball centered at itself.
      refine ⟨y, Metric.mem_ball_self hr, ?_⟩
      simpa [y] using e.left_inv hxsource
    have hs_subset : s ⊆ u := by
      -- Pulling the chosen chart ball back stays inside the original open neighborhood.
      refine hs_subset_u ?_
      exact (Metric.ball_subset_closedBall : Metric.ball y r ⊆ Metric.closedBall y r).trans hclosed
    exact ⟨s, Or.inr hs_precompact, hxs, hs_subset⟩
  · have hy_pos : 0 < y.1 0 := by
      exact lt_of_le_of_ne y.2 (Ne.symm hy_boundary)
    let r' : ℝ := min r (y.1 0 / 2)
    have hr' : 0 < r' := by
      -- Shrinking the radius keeps it positive while moving the ball away from the boundary.
      have hy_half_pos : 0 < y.1 0 / 2 := by
        linarith
      exact lt_min hr hy_half_pos
    have hr'_lt : r' < y.1 0 := by
      -- The shrunken radius is at most half the boundary coordinate, hence strictly smaller.
      have hy_half_lt : y.1 0 / 2 < y.1 0 := by
        linarith
      exact lt_of_le_of_lt (min_le_right _ _) hy_half_lt
    have hclosed' : Metric.closedBall y r' ⊆ w := by
      -- The smaller closed ball still lies in the chosen open chart image.
      exact (Metric.closedBall_subset_closedBall (x := y) (min_le_left _ _)).trans hclosed
    let s : Set M := e.symm '' Metric.ball y r'
    have hs_precompact : IsPrecompactBoundaryModelCoordinateBall (m + 1) s := by
      -- A ball centered away from the boundary hyperplane is a coordinate ball.
      simpa [s, y, r'] using isPrecompactBoundaryModelCoordinateBall_chartPreimageMetricBall
        (M := M) (m := m) e hr' hr'_lt (hclosed'.trans hw_target)
    have hxs : x ∈ s := by
      -- The chart center lies in every positive-radius ball centered at itself.
      refine ⟨y, Metric.mem_ball_self hr', ?_⟩
      simpa [y] using e.left_inv hxsource
    have hs_subset : s ⊆ u := by
      -- Pulling the chosen chart ball back stays inside the original open neighborhood.
      refine hs_subset_u ?_
      exact (Metric.ball_subset_closedBall : Metric.ball y r' ⊆ Metric.closedBall y r').trans
        hclosed'
    exact ⟨s, Or.inl hs_precompact, hxs, hs_subset⟩

/-- Helper for Proposition 1.40: in positive boundary dimension, precompact boundary-model
coordinate balls and half-balls form a topological basis. -/
theorem isTopologicalBasis_precompactBoundaryModelCoordinateBallHalfBall_succ
    {m : ℕ} [TopologicalManifoldWithBoundary (m + 1) M] :
    TopologicalSpace.IsTopologicalBasis
      { s : Set M |
          IsPrecompactBoundaryModelCoordinateBall (m + 1) s ∨
            IsPrecompactBoundaryModelCoordinateHalfBall (m + 1) s } := by
  -- The local chart construction gives a basis element inside every open neighborhood.
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro s hs
    rcases hs with hs | hs
    · rcases hs.1 with ⟨e, rfl, c, r, hr, hc, htarget⟩
      simpa using e.open_source
    · rcases hs.1 with ⟨e, rfl, c, r, hr, hc, htarget⟩
      simpa using e.open_source
  · intro x u hx hu
    exact exists_precompactBoundaryModelCoordinateBallOrHalfBall_subset_of_mem_open_succ
      (M := M) (m := m) hx hu

-- Proof sketch: refine the countable atlas by choosing, inside each chart target, a countable
-- family of rational balls centered either in the interior or on the boundary hyperplane and with
-- compact closure inside the chart domain, then pull them back to `M`.
/-- Clause (1) of Proposition 1.40: a topological manifold with boundary admits a countable basis
consisting of precompact coordinate balls and precompact coordinate half-balls. -/
theorem exists_countable_precompact_coordinate_ball_half_ball_basis :
    ∃ b : Set (Set M),
      b.Countable ∧ IsPrecompactBoundaryModelCoordinateBallHalfBallBasis n b := by
  cases n with
  | zero =>
      letI : TopologicalManifold 0 M := topologicalManifoldOfChartedSpace 0 M
      -- In dimension `0`, Lee's boundary model agrees with the ordinary Euclidean model.
      obtain ⟨b, hbCountable, hbBasis, hbMem⟩ :=
        exists_countable_precompact_coordinate_ball_basis (n := 0) (M := M)
      refine ⟨b, hbCountable, ?_⟩
      refine ⟨hbBasis, ?_⟩
      intro s hs
      exact Or.inl <|
        isPrecompactBoundaryModelCoordinateBall_of_isPrecompactCoordinateBall_zero
          (M := M) (s := s) (hbMem s hs)
  | succ m =>
      let B : Set (Set M) := { s : Set M |
        IsPrecompactBoundaryModelCoordinateBall (m + 1) s ∨
          IsPrecompactBoundaryModelCoordinateHalfBall (m + 1) s }
      have hB : TopologicalSpace.IsTopologicalBasis B := by
        -- In positive dimension, the local chart construction already gives the desired basis.
        exact isTopologicalBasis_precompactBoundaryModelCoordinateBallHalfBall_succ
          (M := M) (m := m)
      obtain ⟨b, hbB, hbCountable, hbBasis⟩ := hB.exists_countable
      refine ⟨b, hbCountable, ?_⟩
      refine ⟨hbBasis, ?_⟩
      intro s hs
      exact hbB hs

section

include n

/-- Helper for Proposition 1.40: local compactness transfers from Lee's boundary model to any
topological manifold with boundary. -/
theorem locallyCompactSpace_of_topologicalManifoldWithBoundary :
    LocallyCompactSpace M := by
  cases n with
  | zero =>
      -- In dimension `0`, the boundary model is the Euclidean model `ℝ^0`.
      exact ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 0)) M
  | succ m =>
      -- In positive dimension, the boundary model is the Euclidean half-space.
      let _ : T2Space (EuclideanHalfSpace (m + 1)) := by
        change T2Space { x : EuclideanSpace ℝ (Fin (m + 1)) // 0 ≤ x 0 }
        infer_instance
      have hcoord :
          Continuous fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0 := by
        exact PiLp.continuous_apply (p := (2 : ℕ∞)) (β := fun _ : Fin (m + 1) => ℝ)
          (i := (0 : Fin (m + 1)))
      have hclosedHalf :
          IsClosed { x : EuclideanSpace ℝ (Fin (m + 1)) | 0 ≤ x 0 } := by
        exact isClosed_le continuous_const hcoord
      let _ : WeaklyLocallyCompactSpace (EuclideanHalfSpace (m + 1)) :=
        hclosedHalf.weaklyLocallyCompactSpace
      let _ : LocallyCompactSpace (EuclideanHalfSpace (m + 1)) := inferInstance
      exact ChartedSpace.locallyCompactSpace (EuclideanHalfSpace (m + 1)) M

/-- Helper for Proposition 1.40: local path-connectedness transfers from Lee's boundary model to
any topological manifold with boundary. -/
theorem locPathConnectedSpace_of_topologicalManifoldWithBoundary :
    LocPathConnectedSpace M := by
  cases n with
  | zero =>
      -- In dimension `0`, the boundary model is the Euclidean model `ℝ^0`.
      exact ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 0)) M
  | succ m =>
      -- In positive dimension, the boundary model is the Euclidean half-space.
      exact ChartedSpace.locPathConnectedSpace (EuclideanHalfSpace (m + 1)) M

/-- Helper for Proposition 1.40: connected components are open once local path-connectedness is
available on the manifold with boundary. -/
theorem connectedComponent_isOpen_of_topologicalManifoldWithBoundary (x : M) :
    IsOpen (connectedComponent x) := by
  letI : LocPathConnectedSpace M :=
    locPathConnectedSpace_of_topologicalManifoldWithBoundary (n := n) (M := M)
  letI : LocallyConnectedSpace M := inferInstance
  exact isOpen_connectedComponent

-- Proof sketch: the model spaces `ℝ^0` and `H^n` are locally compact, and local compactness
-- transfers from the model space to any charted space.
/-- Clause (2) of Proposition 1.40: a topological manifold with boundary is locally compact. -/
theorem topologicalManifoldWithBoundary_locallyCompactSpace : LocallyCompactSpace M := by
  -- This is the direct owner-level local-compactness transfer from the model space.
  exact locallyCompactSpace_of_topologicalManifoldWithBoundary (n := n) (M := M)

-- Proof sketch: combine local compactness from the previous clause with second countability and
-- Hausdorff separation, then apply the standard paracompactness theorem for such spaces.
/-- Clause (3) of Proposition 1.40: a topological manifold with boundary is paracompact. -/
theorem topologicalManifoldWithBoundary_paracompactSpace : ParacompactSpace M := by
  -- Combine local compactness with second countability to obtain `σ`-compactness first.
  letI : LocallyCompactSpace M :=
    topologicalManifoldWithBoundary_locallyCompactSpace (n := n) (M := M)
  letI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  exact paracompact_of_locallyCompact_sigmaCompact

-- Proof sketch: every point has a chart into `ℝ^0` or a Euclidean half-space, and these model
-- spaces are locally path-connected; the property transfers across local homeomorphisms.
/-- Clause (4) of Proposition 1.40: a topological manifold with boundary is locally
path-connected. -/
theorem topologicalManifoldWithBoundaryLocPathConnectedSpace : LocPathConnectedSpace M := by
  -- This is the direct owner-level local-path-connectedness transfer from the model space.
  exact locPathConnectedSpace_of_topologicalManifoldWithBoundary (n := n) (M := M)

/-- Convenience theorem restating the local path-connectedness instance. -/
theorem topologicalManifoldWithBoundary_locPathConnectedSpace : LocPathConnectedSpace M :=
  topologicalManifoldWithBoundaryLocPathConnectedSpace (n := n) (M := M)

/-- The connected component through `x`, regarded as an open subset of the ambient manifold. -/
def connectedComponentOpens (x : M) : TopologicalSpace.Opens M :=
  ⟨connectedComponent x,
    connectedComponent_isOpen_of_topologicalManifoldWithBoundary (n := n) (M := M) x⟩

-- Proof sketch: local path-connectedness makes connected components open, hence the quotient by
-- connected components is discrete; second countability then forces this quotient to be countable.
/-- Clause (5) of Proposition 1.40: a topological manifold with boundary has countably many
connected components. -/
theorem topologicalManifoldWithBoundary_countable_connectedComponents :
    Countable (ConnectedComponents M) := by
  letI : LocPathConnectedSpace M :=
    topologicalManifoldWithBoundary_locPathConnectedSpace (n := n) (M := M)
  letI : LocallyConnectedSpace M := inferInstance
  letI : LindelofSpace M := inferInstance
  letI : DiscreteTopology (ConnectedComponents M) := inferInstance
  letI : LindelofSpace (ConnectedComponents M) :=
    LindelofSpace.of_continuous_surjective ConnectedComponents.continuous_coe
      ConnectedComponents.surjective_coe
  -- The connected-components quotient is discrete and Lindelöf, hence countable.
  exact countable_of_Lindelof_of_discrete

-- Proof sketch: in a locally path-connected space, connected components are open because locally
-- path-connected spaces are locally connected.
/-- Clause (6) of Proposition 1.40: every connected component of a topological manifold with
boundary is an open subset of the manifold. -/
theorem connectedComponent_isOpen (x : M) : IsOpen (connectedComponent x) := by
  -- Local path-connectedness promotes connected components to open sets.
  exact connectedComponent_isOpen_of_topologicalManifoldWithBoundary (n := n) (M := M) x

-- Proof sketch: by definition, the connected component of `x` is the maximal connected subset
-- containing `x`, so its subtype is connected.
/-- Clause (7) of Proposition 1.40: each connected component, viewed as a subtype, is connected. -/
theorem connectedComponent_connectedSpace (x : M) :
    ConnectedSpace (connectedComponentOpens (n := n) (M := M) x) := by
  -- The subtype on a connected component is connected by the canonical connected-component theorem.
  simpa [connectedComponentOpens] using
    (Subtype.connectedSpace
      (show IsConnected (connectedComponent x : Set M) from isConnected_connectedComponent))

-- Proof sketch: once a connected component is viewed as an open subset, it inherits the ambient
-- charts, Hausdorff property, and second-countable topology, hence the same manifold-with-boundary
-- structure.
/-- Clause (8) of Proposition 1.40: each connected component, viewed as an open subset, is a
connected topological manifold with boundary. -/
instance connectedComponent_topologicalManifoldWithBoundary (x : M) :
    TopologicalManifoldWithBoundary n (connectedComponentOpens (n := n) (M := M) x) where
  -- The connected component is an open submanifold, so every owner field is inherited.
  toT2Space := inferInstance
  toSecondCountableTopology := inferInstance
  toChartedSpace := inferInstance
  toIsManifold := inferInstance

end

-- Proof sketch: a second-countable locally path-connected manifold admits a countable loop space
-- model up to homotopy, so the quotient defining the fundamental group at a basepoint is
-- countable.
section

include n

variable {X : Type*} [TopologicalSpace X]

omit n in
/-- Helper for Proposition 1.40: package an ambient path whose image lies in `U` as a path in the
subtype `U`. -/
-- Recording the pointwise membership data once avoids transport noise in later homotopy lemmas.
def pathSubtypeOfMapsTo {U : Set X} {x y : X} (p : Path x y)
    (hx : x ∈ U) (hy : y ∈ U) (hp : ∀ t, p t ∈ U) :
    Path (⟨x, hx⟩ : U) (⟨y, hy⟩ : U) :=
  { toContinuousMap := ⟨fun t ↦ ⟨p t, hp t⟩, Continuous.subtype_mk p.continuous fun t ↦ hp t⟩
    source' := Subtype.ext p.source
    target' := Subtype.ext p.target }

omit n in
/-- Helper for Proposition 1.40: mapping the subtype path `pathSubtypeOfMapsTo` back to the ambient
space recovers the original path. -/
theorem pathSubtypeOfMapsTo_map_subtypeVal {U : Set X} {x y : X} (p : Path x y)
    (hx : x ∈ U) (hy : y ∈ U) (hp : ∀ t, p t ∈ U) :
    (pathSubtypeOfMapsTo p hx hy hp).map (ContinuousMap.restrict U (.id X)).continuous = p := by
  -- Both paths have the same underlying map `I → X`, so extensionality closes the comparison.
  ext t
  rfl

omit n in
/-- Helper for Proposition 1.40: any two ambient paths with image inside the same contractible set
are homotopic. -/
theorem pathHomotopic_of_mapsTo_contractibleOpen {U : Set X} [ContractibleSpace U] {x y : X}
    (p q : Path x y) (hp : ∀ t, p t ∈ U) (hq : ∀ t, q t ∈ U) :
    p.Homotopic q := by
  have hx : x ∈ U := by
    simpa using hp 0
  have hy : y ∈ U := by
    simpa using hp 1
  let pU : Path (⟨x, hx⟩ : U) (⟨y, hy⟩ : U) := pathSubtypeOfMapsTo p hx hy hp
  let qU : Path (⟨x, hx⟩ : U) (⟨y, hy⟩ : U) := pathSubtypeOfMapsTo q hx hy hq
  have hpqU : pU.Homotopic qU := by
    -- Contractible subtype spaces are simply connected, so their path classes are unique.
    exact SimplyConnectedSpace.paths_homotopic pU qU
  -- Mapping the homotopy back along the subtype inclusion returns the original ambient paths.
  simpa [pU, qU, pathSubtypeOfMapsTo_map_subtypeVal] using
    Path.Homotopic.map hpqU (ContinuousMap.restrict U (.id X))

omit n in
/-- Helper for Proposition 1.40: an open subset of a second-countable locally path-connected space
has countably many connected components. -/
theorem countableConnectedComponents_of_isOpen [SecondCountableTopology X]
    [LocPathConnectedSpace X] {U : Set X} (hU : IsOpen U) :
    Countable (ConnectedComponents U) := by
  letI : LocPathConnectedSpace U := hU.locPathConnectedSpace
  letI : LocallyConnectedSpace U := inferInstance
  letI : LindelofSpace U := inferInstance
  letI : DiscreteTopology (ConnectedComponents U) := inferInstance
  letI : LindelofSpace (ConnectedComponents U) :=
    LindelofSpace.of_continuous_surjective ConnectedComponents.continuous_coe
      ConnectedComponents.surjective_coe
  -- The connected-components quotient is discrete and Lindelöf, hence countable.
  exact countable_of_Lindelof_of_discrete

omit n in
/-- Helper for Proposition 1.40: every metric ball in `EuclideanHalfSpace k` is contractible,
because its image in the ambient Euclidean space is the intersection of two convex sets. -/
theorem contractibleSpace_metricBall_euclideanHalfSpace {k : ℕ} [NeZero k]
    (c : EuclideanHalfSpace k) {r : ℝ} (hr : 0 < r) :
    ContractibleSpace (Metric.ball c r : Set (EuclideanHalfSpace k)) := by
  let E := EuclideanSpace ℝ (Fin k)
  have himage :
      (Subtype.val '' (Metric.ball c r : Set (EuclideanHalfSpace k))) =
        ({x : E | 0 ≤ x 0} ∩ Metric.ball c.1 r) := by
    -- The subtype ball is exactly the ambient Euclidean ball cut out by the half-space inequality.
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      constructor
      · exact y.2
      · simpa [Metric.mem_ball, Subtype.dist_eq] using hy
    · rintro ⟨hxhalf, hxball⟩
      refine ⟨⟨x, hxhalf⟩, ?_, rfl⟩
      simpa [Metric.mem_ball, Subtype.dist_eq] using hxball
  have hconvex :
      Convex ℝ ({x : E | 0 ≤ x 0} ∩ Metric.ball c.1 r) := by
    -- Both the ambient half-space and the Euclidean open ball are convex.
    refine EuclideanHalfSpace.convex.inter ?_
    simpa using (convex_ball c.1 r)
  have hnonempty : ({x : E | 0 ≤ x 0} ∩ Metric.ball c.1 r).Nonempty := by
    -- The center belongs to the ambient image because the radius is positive.
    refine ⟨c.1, ?_⟩
    constructor
    · exact c.2
    · exact Metric.mem_ball_self hr
  have himage_contractible :
      ContractibleSpace (Subtype.val '' (Metric.ball c r : Set (EuclideanHalfSpace k))) := by
    let e :
        (Subtype.val '' (Metric.ball c r : Set (EuclideanHalfSpace k))) ≃ₜ
          ((({x : E | 0 ≤ x 0} ∩ Metric.ball c.1 r) : Set E)) :=
      Homeomorph.setCongr himage
    exact e.contractibleSpace_iff.mpr (hconvex.contractibleSpace hnonempty)
  let e :
      (Metric.ball c r : Set (EuclideanHalfSpace k)) ≃ₜ
        (Subtype.val '' (Metric.ball c r : Set (EuclideanHalfSpace k))) :=
    Topology.IsEmbedding.subtypeVal.homeomorphImage
      (Metric.ball c r : Set (EuclideanHalfSpace k))
  -- Transport contractibility back across the embedding homeomorphism.
  exact e.contractibleSpace_iff.mpr himage_contractible

/-- Helper for Proposition 1.40: every boundary-model coordinate ball or half-ball is
contractible. -/
theorem contractibleSpace_of_boundaryModelCoordinateBallOrHalfBall {s : Set M}
    (hs :
      IsBoundaryModelCoordinateBall n s ∨
        IsBoundaryModelCoordinateHalfBall n s) :
    ContractibleSpace s := by
  cases n with
  | zero =>
      rcases hs with hsBall | hsHalf
      · rcases hsBall with ⟨e, hsource, c, r, hr, htarget⟩
        let hst :
            s ≃ₜ (Metric.ball c r : Set (EuclideanSpace ℝ (Fin 0))) :=
          (Homeomorph.setCongr hsource.symm).trans
            (e.toHomeomorphSourceTarget.trans (Homeomorph.setCongr htarget))
        let _ : ContractibleSpace (Metric.ball c r : Set (EuclideanSpace ℝ (Fin 0))) :=
          Metric.contractibleSpace_ball hr
        -- The chart identifies `s` with an ordinary Euclidean open ball.
        exact hst.contractibleSpace
      · cases hsHalf
  | succ m =>
      rcases hs with hsBall | hsHalf
      · rcases hsBall with ⟨e, hsource, c, r, hr, _hc, htarget⟩
        let hst :
            s ≃ₜ (Metric.ball c r : Set (EuclideanHalfSpace (m + 1))) :=
          (Homeomorph.setCongr hsource.symm).trans
            (e.toHomeomorphSourceTarget.trans (Homeomorph.setCongr htarget))
        let _ : ContractibleSpace (Metric.ball c r : Set (EuclideanHalfSpace (m + 1))) :=
          contractibleSpace_metricBall_euclideanHalfSpace c hr
        -- Positive-dimensional coordinate balls are chart-preimages of contractible model balls.
        exact hst.contractibleSpace
      · rcases hsHalf with ⟨e, hsource, c, r, hr, _hc, htarget⟩
        let hst :
            s ≃ₜ (Metric.ball c r : Set (EuclideanHalfSpace (m + 1))) :=
          (Homeomorph.setCongr hsource.symm).trans
            (e.toHomeomorphSourceTarget.trans (Homeomorph.setCongr htarget))
        let _ : ContractibleSpace (Metric.ball c r : Set (EuclideanHalfSpace (m + 1))) :=
          contractibleSpace_metricBall_euclideanHalfSpace c hr
        -- Positive-dimensional coordinate half-balls use the same contractible model target.
        exact hst.contractibleSpace

/-- Helper for Proposition 1.40: a loop code of length `n + 1` records `n + 1` basis elements and
`n` overlap markers drawn from a chosen countable subset. -/
def contractibleBasisLoopCodeData {b : Set (Set X)} (d : Set X) (n : ℕ) : Type _ :=
  (Fin (n + 1) → { s : Set X // s ∈ b }) × (Fin n → d)

omit n in
/-- Helper for Proposition 1.40: the tail of a loop code forgets the first basis element and the
first overlap marker. -/
def contractibleBasisLoopCodeTail {b : Set (Set X)} {d : Set X} {n : ℕ}
    (code : contractibleBasisLoopCodeData (X := X) (b := b) d (n + 1)) :
    contractibleBasisLoopCodeData (X := X) (b := b) d n :=
  (fun i ↦ code.1 i.succ, fun i ↦ code.2 i.succ)

omit n in
/-- Helper for Proposition 1.40: a path realizes a loop code when it is homotopic to a
concatenation whose successive pieces lie in the recorded contractible basis elements. -/
def contractibleBasisLoopCodeData.Realizes {b : Set (Set X)} {d : Set X} :
    ∀ {n : ℕ}, contractibleBasisLoopCodeData (X := X) (b := b) d n → ∀ {a z : X}, Path a z → Prop
  | 0, code, _a, _z, p => ∀ t, p t ∈ (code.1 0).1
  | _m + 1, code, a, z, p =>
      ∃ q : Path a (code.2 0).1, ∃ r : Path (code.2 0).1 z,
        (∀ t, q t ∈ (code.1 0).1) ∧
        (contractibleBasisLoopCodeTail code).Realizes r ∧
        p.Homotopic (q.trans r)

omit n in
/-- Helper for Proposition 1.40: the ambient loop-code type is the sigma union of all finite code
lengths. -/
def contractibleBasisLoopCode {b : Set (Set X)} (d : Set X) : Type _ :=
  PSigma fun n : ℕ ↦ contractibleBasisLoopCodeData (X := X) (b := b) d n

omit n in
/-- Helper for Proposition 1.40: a loop realizes a sigma-coded loop code when it realizes the code
data in the corresponding length fiber. -/
def contractibleBasisLoopCode.Realizes {b : Set (Set X)} {d : Set X}
    (code : contractibleBasisLoopCode (X := X) (b := b) d) {a z : X} (p : Path a z) : Prop :=
  code.2.Realizes p

omit [TopologicalSpace X] n in
/-- Helper for Proposition 1.40: the ambient contractible-basis loop-code type is countable when
both the basis and the marker set are countable. -/
theorem countable_contractibleBasisLoopCodeData {b : Set (Set X)} {d : Set X}
    (hbCountable : b.Countable) (hdCountable : d.Countable) (n : ℕ) :
    Countable (contractibleBasisLoopCodeData (X := X) (b := b) d n) := by
  -- Each fixed-length code is a finite product of countable types.
  let _ : Countable { s : Set X // s ∈ b } := hbCountable.to_subtype
  let _ : Countable d := hdCountable.to_subtype
  dsimp [contractibleBasisLoopCodeData]
  infer_instance

omit [TopologicalSpace X] n in
/-- Helper for Proposition 1.40: the ambient contractible-basis loop-code type is countable when
both the basis and the marker set are countable. -/
theorem countable_contractibleBasisLoopCode {b : Set (Set X)} {d : Set X}
    (hbCountable : b.Countable) (hdCountable : d.Countable) :
    Countable (contractibleBasisLoopCode (X := X) (b := b) d) := by
  -- The code space is a countable sigma type of finite products of countable types.
  let _ : ∀ n : ℕ, Countable (contractibleBasisLoopCodeData (X := X) (b := b) d n) := fun n ↦
    countable_contractibleBasisLoopCodeData (X := X) (b := b) (d := d) hbCountable hdCountable n
  simpa [contractibleBasisLoopCode] using
    (inferInstance :
      Countable (PSigma fun n : ℕ ↦ contractibleBasisLoopCodeData (X := X) (b := b) d n))

omit n in
/-- Helper for Proposition 1.40: the realizable-code subtype remains countable because it is a
subtype of the ambient countable code space. -/
theorem countable_realizableContractibleBasisLoopCode {b : Set (Set X)} {d : Set X} (x : X)
    (hbCountable : b.Countable) (hdCountable : d.Countable) :
    Countable { code : contractibleBasisLoopCode (X := X) (b := b) d //
      ∃ p : Path x x, contractibleBasisLoopCode.Realizes code p } := by
  -- Once the ambient code space is countable, the subtype inherits countability.
  let _ : Countable (contractibleBasisLoopCode (X := X) (b := b) d) :=
    countable_contractibleBasisLoopCode (X := X) (b := b) (d := d) hbCountable hdCountable
  infer_instance

omit n in
/-- Helper for Proposition 1.40: any two points in the same contractible basis element can be
joined by a path staying inside that basis element. -/
theorem exists_pathWithinContractibleBasis {b : Set (Set X)}
    (hbContractible : ∀ s ∈ b, ContractibleSpace s) (U : { s : Set X // s ∈ b }) {a z : X}
    (ha : a ∈ U.1) (hz : z ∈ U.1) : ∃ p : Path a z, ∀ t, p t ∈ U.1 := by
  -- Work in the contractible subtype.
  -- Then map the chosen subtype path back to the ambient space.
  let _ : ContractibleSpace U.1 := hbContractible U.1 U.2
  let p : Path (⟨a, ha⟩ : U.1) (⟨z, hz⟩ : U.1) := PathConnectedSpace.somePath _ _
  refine ⟨p.map continuous_subtype_val, ?_⟩
  intro t
  exact (p t).2

omit n in
/-- Helper for Proposition 1.40: once a contractible-basis loop code is fixed, any two paths that
realize it are homotopic. -/
theorem realizesContractibleBasisLoopCodeData_homotopic {b : Set (Set X)} {d : Set X}
    (hbContractible : ∀ s ∈ b, ContractibleSpace s) :
    ∀ {n : ℕ} {code : contractibleBasisLoopCodeData (X := X) (b := b) d n} {a z : X}
      {p q : Path a z},
      code.Realizes p → code.Realizes q → p.Homotopic q := by
  intro n
  induction n with
  | zero =>
      intro code a z p q hp hq
      -- In the one-segment case, both paths lie in the same contractible basis element.
      rcases code with ⟨U, _markers⟩
      let _ : ContractibleSpace (U 0).1 := hbContractible (U 0).1 (U 0).2
      simpa using pathHomotopic_of_mapsTo_contractibleOpen (U := (U 0).1) p q hp hq
  | succ n ih =>
      intro code a z p q hp hq
      -- Compare the first segments inside one contractible basis element and recurse on the tail.
      rcases code with ⟨U, y⟩
      rcases hp with ⟨p₀, p₁, hp₀, hp₁, hpConcat⟩
      rcases hq with ⟨q₀, q₁, hq₀, hq₁, hqConcat⟩
      let _ : ContractibleSpace (U 0).1 := hbContractible (U 0).1 (U 0).2
      have hFirst : p₀.Homotopic q₀ := by
        simpa using pathHomotopic_of_mapsTo_contractibleOpen (U := (U 0).1) p₀ q₀ hp₀ hq₀
      have hTail : p₁.Homotopic q₁ := by
        exact ih (code := contractibleBasisLoopCodeTail (X := X) (b := b) (d := d) (U, y))
          hp₁ hq₁
      exact hpConcat.trans ((hFirst.hcomp hTail).trans hqConcat.symm)

omit n in
/-- Helper for Proposition 1.40: front-recursive concatenation of a finite compatible path chain. -/
def segmentChainPath :
    ∀ {m : ℕ} {z : Fin (m + 2) → X},
      ((i : Fin (m + 1)) → Path (z i.castSucc) (z i.succ)) →
        Path (z 0) (z (Fin.last (m + 1)))
  | 0, _z, σ => σ 0
  | _ + 1, z, σ =>
      (σ 0).trans
        (segmentChainPath (z := Fin.tail z) (fun i ↦ σ i.succ))

omit n in
/-- Helper for Proposition 1.40: casting a realized path along endpoint equalities preserves the
realization relation. -/
theorem contractibleBasisLoopCodeData.realizes_cast {b : Set (Set X)} {d : Set X} {m : ℕ}
    {code : contractibleBasisLoopCodeData (X := X) (b := b) d m} {a z a' z' : X}
    {p : Path a z} (hp : code.Realizes p) (ha : a' = a) (hz : z' = z) :
    code.Realizes (p.cast ha hz) := by
  -- After transporting the endpoints, the realizing path is unchanged as a function.
  subst ha
  subst hz
  simpa using hp

omit n in
/-- Helper for Proposition 1.40: homotopies are preserved when both endpoint equalities are used
to cast the compared paths. -/
theorem pathHomotopic_cast {a z a' z' : X} {p q : Path a z} (hpq : p.Homotopic q)
    (ha : a' = a) (hz : z' = z) :
    (p.cast ha hz).Homotopic (q.cast ha hz) := by
  -- This is pure endpoint transport, so substituting the equalities reduces to the original proof.
  subst ha
  subst hz
  simpa using hpq

omit n in
/-- Helper for Proposition 1.40: a dense marker can be chosen inside the overlap path-component of
an overlap point. -/
theorem existsDenseMarkerJoinedInOverlap {d : Set X} (hdDense : Dense d) {U V : Set X}
    [LocPathConnectedSpace X] (hU : IsOpen U) (hV : IsOpen V) {z : X} (hz : z ∈ U ∩ V) :
    ∃ y : d, JoinedIn (U ∩ V) z y.1 := by
  let W := pathComponentIn (U ∩ V) z
  have hWOpen : IsOpen W := (hU.inter hV).pathComponentIn z
  have hzW : z ∈ W := mem_pathComponentIn_self hz
  obtain ⟨y, hyd, hyW⟩ := hdDense.exists_mem_open hWOpen ⟨z, hzW⟩
  exact ⟨⟨y, hyd⟩, hyW⟩

omit n in
/-- Helper for Proposition 1.40: the front-recursive chain of consecutive subpaths recovers the
whole path up to homotopy. -/
theorem segmentChainPath_subpath_homotopic {a z : X} (γ : Path a z) :
    ∀ {m : ℕ} (t : Fin (m + 2) → ↥unitInterval),
      (segmentChainPath (z := fun i ↦ γ (t i))
          (fun i ↦ γ.subpath (t i.castSucc) (t i.succ))).Homotopic
        (γ.subpath (t 0) (t (Fin.last (m + 1)))) := by
  intro m
  induction m with
  | zero =>
      intro t
      -- In the single-segment case, the chain is exactly that subpath.
      simpa [segmentChainPath] using
        (Path.Homotopic.refl (γ.subpath (t 0) (t 1)))
  | succ m ih =>
      intro t
      -- Split off the first subpath, collapse the tail inductively, then compose adjacent
      -- subpaths back together.
      simpa [segmentChainPath] using
        (((Path.Homotopic.refl (γ.subpath (t 0) (t 1))).hcomp (ih (Fin.tail t))).trans
          ⟨Path.Homotopy.subpathTransSubpath γ (t 0) (t 1) (t (Fin.last (m + 2)))⟩)

omit n in
/-- Helper for Proposition 1.40: inserting a bridge and its reverse at the first breakpoint of a
front-recursive segment chain does not change its homotopy class. -/
theorem segmentChainPath_insertBridge_homotopic {n : ℕ} {z : Fin (n + 3) → X}
    (σ : (i : Fin (n + 2)) → Path (z i.castSucc) (z i.succ)) {y : X}
    (g : Path (z 1) y) :
    (segmentChainPath (z := Fin.tail z) (fun i ↦ σ i.succ)).Homotopic
      (g.trans
        (segmentChainPath
          (z := Fin.cons y (fun i : Fin (n + 1) ↦ z i.succ.succ))
          (Fin.cons (g.symm.trans (σ 1)) (fun i : Fin n ↦ σ i.succ.succ)))) := by
  cases n with
  | zero =>
      -- With only one remaining segment, the bridge cancels against its reverse directly.
      simpa [segmentChainPath] using
        (((Path.Homotopic.refl_trans (σ 1)).symm.trans
          ((((Path.Homotopic.trans_symm g).symm).hcomp (Path.Homotopic.refl (σ 1))).trans
            (Path.Homotopic.trans_assoc g g.symm (σ 1)))))
  | succ n =>
      -- For longer chains, only the first breakpoint changes; the rest of the chain is unchanged.
      let rest :
          Path (z 2) (z (Fin.last (n + 3))) :=
        segmentChainPath (z := fun i : Fin (n + 2) ↦ z i.succ.succ)
          (fun i : Fin (n + 1) ↦ σ i.succ.succ)
      have hInsert :
          ((σ 1).trans rest).Homotopic (((Path.refl (z 1)).trans (σ 1)).trans rest) := by
        exact ((Path.Homotopic.refl_trans (σ 1)).symm).hcomp (Path.Homotopic.refl rest)
      have hExpand :
          (((Path.refl (z 1)).trans (σ 1)).trans rest).Homotopic
            ((((g.trans g.symm).trans (σ 1)).trans rest)) := by
        exact ((((Path.Homotopic.trans_symm g).symm).hcomp
            (Path.Homotopic.refl (σ 1))).hcomp (Path.Homotopic.refl rest))
      have hAssoc₁ :
          ((((g.trans g.symm).trans (σ 1)).trans rest)).Homotopic
            (((g.trans (g.symm.trans (σ 1))).trans rest)) := by
        exact (Path.Homotopic.trans_assoc g g.symm (σ 1)).hcomp (Path.Homotopic.refl rest)
      have hAssoc₂ :
          (((g.trans (g.symm.trans (σ 1))).trans rest)).Homotopic
            (g.trans ((g.symm.trans (σ 1)).trans rest)) := by
        exact Path.Homotopic.trans_assoc g (g.symm.trans (σ 1)) rest
      simpa [segmentChainPath, rest] using hInsert.trans (hExpand.trans (hAssoc₁.trans hAssoc₂))

omit n in
/-- Helper for Proposition 1.40: a finite chain of path segments contained in contractible basis
elements can be replaced by a realizable dense-marker loop code with the same endpoints. -/
theorem existsRealizesContractibleBasisLoopCodeDataOfSegmentChain {b : Set (Set X)} {d : Set X}
    (hbBasis : TopologicalSpace.IsTopologicalBasis b)
    (hbContractible : ∀ s ∈ b, ContractibleSpace s) [LocPathConnectedSpace X]
    (hdDense : Dense d) {m : ℕ}
    (U : Fin (m + 1) → { s : Set X // s ∈ b }) {z : Fin (m + 2) → X}
    (σ : (i : Fin (m + 1)) → Path (z i.castSucc) (z i.succ))
    (hσ : ∀ i t, σ i t ∈ (U i).1) :
    ∃ y : Fin m → d, ∃ p : Path (z 0) (z (Fin.last (m + 1))),
      contractibleBasisLoopCodeData.Realizes (X := X) (b := b) (d := d)
        ((U, y) : contractibleBasisLoopCodeData (X := X) (b := b) d m) p ∧
        (segmentChainPath (z := z) σ).Homotopic p := by
  induction m with
  | zero =>
      -- A one-segment chain is already a realizing code of length zero.
      refine ⟨Fin.elim0, σ 0, ?_, ?_⟩
      · intro t
        simpa [contractibleBasisLoopCodeData.Realizes] using hσ 0 t
      · simpa [segmentChainPath] using Path.Homotopic.refl (σ 0)
  | succ m ih =>
      have hz₁U₀ : z 1 ∈ (U 0).1 := by
        exact (σ 0).target ▸ hσ 0 1
      have hz₁U₁ : z 1 ∈ (U 1).1 := by
        exact (σ 1).source ▸ hσ 1 0
      obtain ⟨y₀, hy₀⟩ :=
        existsDenseMarkerJoinedInOverlap (X := X) (d := d) hdDense
          (hbBasis.isOpen (U 0).2) (hbBasis.isOpen (U 1).2) ⟨hz₁U₀, hz₁U₁⟩
      have hz₀U₀ : z 0 ∈ (U 0).1 := by
        exact (σ 0).source ▸ hσ 0 0
      have hy₀U₀ : y₀.1 ∈ (U 0).1 := hy₀.target_mem.1
      obtain ⟨q₀, hq₀⟩ :=
        exists_pathWithinContractibleBasis (X := X) (b := b) hbContractible (U 0) hz₀U₀ hy₀U₀
      let UTail : Fin (m + 1) → { s : Set X // s ∈ b } := Fin.tail U
      let zTail : Fin (m + 2) → X :=
        Fin.cons y₀.1 (fun i : Fin (m + 1) ↦ z i.succ.succ)
      let σTail : (i : Fin (m + 1)) → Path (zTail i.castSucc) (zTail i.succ) :=
        Fin.cons (hy₀.somePath.symm.trans (σ 1)) (fun i : Fin m ↦ σ i.succ.succ)
      have hσTail : ∀ i t, σTail i t ∈ (UTail i).1 := by
        intro i t
        refine Fin.cases ?_ ?_ i
        · -- The modified first tail segment stays in the overlap, hence in `U 1`.
          change ((hy₀.somePath.symm.trans (σ 1)) t) ∈ (UTail 0).1
          rw [Path.trans_apply]
          split_ifs with ht
          · simpa [Path.symm_apply] using (hy₀.somePath_mem (unitInterval.symm _)).2
          · exact hσ 1 _
        · intro i
          simpa [σTail, UTail] using hσ i.succ.succ t
      obtain ⟨yTail, r, hrRealizes, hTail⟩ :=
        ih UTail (z := zTail) σTail hσTail
      have hFirstMapsTo : ∀ t, ((σ 0).trans hy₀.somePath) t ∈ (U 0).1 := by
        intro t
        rw [Path.trans_apply]
        split_ifs with ht
        · exact hσ 0 _
        · exact (hy₀.somePath_mem _).1
      have hFirst :
          ((σ 0).trans hy₀.somePath).Homotopic q₀ := by
        -- The contractibility of the first basis element identifies all paths with the same
        -- endpoints inside that open set.
        let _ : ContractibleSpace (U 0).1 := hbContractible (U 0).1 (U 0).2
        simpa using pathHomotopic_of_mapsTo_contractibleOpen (U := (U 0).1)
          ((σ 0).trans hy₀.somePath) q₀ hFirstMapsTo hq₀
      have hTailInsert :
          (segmentChainPath (z := Fin.tail z) (fun i ↦ σ i.succ)).Homotopic
            (hy₀.somePath.trans (segmentChainPath (z := zTail) σTail)) := by
        simpa [σTail, zTail] using
          segmentChainPath_insertBridge_homotopic (X := X) (σ := σ) hy₀.somePath
      have hTailToRealized :
          (segmentChainPath (z := Fin.tail z) (fun i ↦ σ i.succ)).Homotopic
            (hy₀.somePath.trans r) := by
        exact hTailInsert.trans ((Path.Homotopic.refl hy₀.somePath).hcomp hTail)
      refine ⟨Fin.cons y₀ yTail, q₀.trans r, ?_, ?_⟩
      · -- The realizing path is the chosen first segment followed by the recursively realized tail.
        change contractibleBasisLoopCodeData.Realizes (X := X) (b := b) (d := d)
          (((U, Fin.cons y₀ yTail) :
            contractibleBasisLoopCodeData (X := X) (b := b) d (m + 1))) (q₀.trans r)
        refine ⟨q₀, r, hq₀, ?_, Path.Homotopic.refl _⟩
        simpa [contractibleBasisLoopCodeTail, UTail] using hrRealizes
      · -- Compare the original chain to the realized one by inserting the first bridge, replacing
        -- the first segment inside `U 0`, and reusing the recursive tail comparison.
        have hWhole₁ :
            (segmentChainPath (z := z) σ).Homotopic ((σ 0).trans (hy₀.somePath.trans r)) := by
          simpa [segmentChainPath] using (Path.Homotopic.refl (σ 0)).hcomp hTailToRealized
        have hWhole₂ :
            ((σ 0).trans (hy₀.somePath.trans r)).Homotopic
              (((σ 0).trans hy₀.somePath).trans r) := by
          exact (Path.Homotopic.trans_assoc (σ 0) hy₀.somePath r).symm
        have hWhole₃ :
            (((σ 0).trans hy₀.somePath).trans r).Homotopic (q₀.trans r) := by
          exact hFirst.hcomp (Path.Homotopic.refl r)
        exact hWhole₁.trans (hWhole₂.trans hWhole₃)

omit n in
/-- Helper for Proposition 1.40: every path is homotopic to one realized by a dense-marker code
built from a countable contractible basis. -/
theorem existsRealizableContractibleBasisLoopCodeOfPath {b : Set (Set X)} {d : Set X}
    (hbBasis : TopologicalSpace.IsTopologicalBasis b)
    (hbContractible : ∀ s ∈ b, ContractibleSpace s) [LocPathConnectedSpace X]
    (hdDense : Dense d)
    {a z : X} (γ : Path a z) :
    ∃ code : contractibleBasisLoopCode (X := X) (b := b) d, ∃ p : Path a z,
      code.Realizes p ∧ γ.Homotopic p := by
  classical
  let c : { s : Set X // s ∈ b } → Set (↥unitInterval) := fun U ↦ γ ⁻¹' U.1
  have hc₁ : ∀ U, IsOpen (c U) := by
    intro U
    simpa [c] using (hbBasis.isOpen U.2).preimage γ.continuous
  have hc₂ : univ ⊆ ⋃ U, c U := by
    intro t ht
    obtain ⟨U, hUb, hγU, _⟩ :=
      hbBasis.exists_subset_of_mem_open (show γ t ∈ (univ : Set X) by simp) isOpen_univ
    exact Set.mem_iUnion.2 ⟨⟨U, hUb⟩, hγU⟩
  obtain ⟨t, ht₀, htMono, hEventually, htSub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc₁ hc₂
  let N := Nat.find hEventually
  have hN : t N = 1 := (Nat.find_spec hEventually) N le_rfl
  have hN_ne_zero : N ≠ 0 := by
    intro hZero
    have h01 : (0 : ↥unitInterval) = 1 := by
      have hN' := hN
      rwa [hZero, ht₀] at hN'
    exact zero_ne_one h01
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hN_ne_zero
  subst N
  let U : Fin (m + 1) → { s : Set X // s ∈ b } := fun i ↦ Classical.choose (htSub i)
  have hU :
      ∀ i : Fin (m + 1), Icc (t i) (t (i + 1)) ⊆ c (U i) := by
    intro i
    exact Classical.choose_spec (htSub i)
  let σ : (i : Fin (m + 1)) → Path ((fun j : Fin (m + 2) ↦ γ (t j)) i.castSucc)
      ((fun j : Fin (m + 2) ↦ γ (t j)) i.succ) :=
    fun i ↦ γ.subpath (t i.castSucc) (t i.succ)
  have hσ : ∀ i t', σ i t' ∈ (U i).1 := by
    intro i t'
    have hmem :
        σ i t' ∈ Set.range (σ i) := ⟨t', rfl⟩
    rw [show Set.range (σ i) = γ '' Icc (t i.castSucc) (t i.succ) by
      simpa [σ] using
        (Path.range_subpath_of_le γ (t i.castSucc) (t i.succ) (htMono i.castSucc_le_succ))] at hmem
    rcases hmem with ⟨s, hs, hsEq⟩
    exact hsEq.symm ▸ (hU i hs)
  obtain ⟨y, pRaw, hpRaw, hChainRaw⟩ :=
    existsRealizesContractibleBasisLoopCodeDataOfSegmentChain (X := X) (b := b) (d := d)
      hbBasis hbContractible hdDense U (z := fun i : Fin (m + 2) ↦ γ (t i)) σ hσ
  let code : contractibleBasisLoopCode (X := X) (b := b) d := ⟨m, (U, y)⟩
  have hStart : γ (t 0) = a := by
    rw [ht₀]
    exact γ.source
  have hLast : t (m + 1) = 1 := by
    simpa [hm] using hN
  have hLastFin : t (Fin.last (m + 1)) = 1 := by
    simpa using hLast
  have hEnd : γ (t (Fin.last (m + 1))) = z := by
    rw [hLastFin]
    exact γ.target
  let chain : Path a z :=
    Path.cast (segmentChainPath (z := fun i : Fin (m + 2) ↦ γ (t i)) σ) hStart.symm hEnd.symm
  let p : Path a z := by
    exact pRaw.cast hStart.symm hEnd.symm
  have hp : code.Realizes p := by
    simpa [code, p, contractibleBasisLoopCode.Realizes] using
      contractibleBasisLoopCodeData.realizes_cast (X := X) (b := b) (d := d) hpRaw
        hStart.symm hEnd.symm
  have hSubpath : γ.Homotopic chain := by
    -- The subdivision chain recovers `γ.subpath 0 1`, and endpoint casting returns `γ`.
    have hRaw :
        (γ.subpath (t 0) (t (Fin.last (m + 1)))).Homotopic
          (segmentChainPath (z := fun i : Fin (m + 2) ↦ γ (t i)) σ) := by
      exact (segmentChainPath_subpath_homotopic (γ := γ) (fun i : Fin (m + 2) ↦ t i)).symm
    have hCast :
        (Path.cast (γ.subpath (t 0) (t (Fin.last (m + 1)))) hStart.symm hEnd.symm).Homotopic
          chain := by
      exact pathHomotopic_cast (X := X) hRaw hStart.symm hEnd.symm
    have hSubpathEq :
        Path.cast (γ.subpath (t 0) (t (Fin.last (m + 1)))) hStart.symm hEnd.symm = γ := by
      -- The full subdivision runs from `0` to `1`, so casting the resulting full subpath recovers
      -- the original path.
      ext s
      simp [Path.subpath, ht₀, hLast]
    exact hSubpathEq ▸ hCast
  have hRealized : chain.Homotopic p := by
    simpa [chain, p] using pathHomotopic_cast (X := X) hChainRaw hStart.symm hEnd.symm
  exact ⟨code, p, hp, hSubpath.trans hRealized⟩

omit n in
/-- Helper for Proposition 1.40: the realizable dense-marker code subtype surjects onto the
fundamental group. -/
theorem surjectiveRealizableContractibleBasisLoopCode {b : Set (Set X)} {d : Set X}
    (hbBasis : TopologicalSpace.IsTopologicalBasis b)
    (hbContractible : ∀ s ∈ b, ContractibleSpace s) [LocPathConnectedSpace X]
    (hdDense : Dense d) (x : X) :
    Function.Surjective
      (fun code :
        { code : contractibleBasisLoopCode (X := X) (b := b) d //
          ∃ p : Path x x, code.Realizes p } =>
          FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (Classical.choose code.2))) := by
  classical
  intro g
  rcases Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g) with ⟨γ, rfl⟩
  obtain ⟨code, p, hp, hγp⟩ :=
    existsRealizableContractibleBasisLoopCodeOfPath (X := X) (b := b) (d := d)
      hbBasis hbContractible hdDense γ
  refine ⟨⟨code, ⟨p, hp⟩⟩, ?_⟩
  cases code with
  | mk m data =>
      have hChosen :
          data.Realizes (Classical.choose (show ∃ q : Path x x, data.Realizes q from ⟨p, hp⟩)) := by
        exact Classical.choose_spec (show ∃ q : Path x x, data.Realizes q from ⟨p, hp⟩)
      have hCode :
          (Classical.choose (show ∃ q : Path x x, data.Realizes q from ⟨p, hp⟩)).Homotopic p := by
        simpa using realizesContractibleBasisLoopCodeData_homotopic
          (X := X) (b := b) (d := d) hbContractible hChosen hp
      have hChosenEq :
          FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.mk
                (Classical.choose (show ∃ q : Path x x, data.Realizes q from ⟨p, hp⟩))) =
            FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) := by
        apply congrArg FundamentalGroup.fromPath
        exact (Path.Homotopic.Quotient.eq).2 hCode
      have hpEq :
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) =
            FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) := by
        apply congrArg FundamentalGroup.fromPath
        exact (Path.Homotopic.Quotient.eq).2 hγp.symm
      simpa [contractibleBasisLoopCode.Realizes] using hChosenEq.trans hpEq

omit n in
/-- Proposition 1.40: a second-countable locally path-connected space with a countable basis of
contractible opens has countable fundamental group. -/
theorem countable_fundamentalGroup_of_countable_contractible_basis
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X] [LocPathConnectedSpace X]
    (x : X) {b : Set (Set X)} (hbCountable : b.Countable)
    (hbBasis : TopologicalSpace.IsTopologicalBasis b)
    (hbContractible : ∀ s ∈ b, ContractibleSpace s) :
    Countable (FundamentalGroup X x) := by
  obtain ⟨d, hdCountable, hdDense⟩ := TopologicalSpace.exists_countable_dense X
  have hCodeCountable :
      Countable { code : contractibleBasisLoopCode (X := X) (b := b) d //
        ∃ p : Path x x, contractibleBasisLoopCode.Realizes code p } := by
    -- The eventual source of the surjection is already a countable subtype.
    exact countable_realizableContractibleBasisLoopCode (X := X) (b := b) (d := d) x
      hbCountable hdCountable
  classical
  let F :
      { code : contractibleBasisLoopCode (X := X) (b := b) d //
        ∃ p : Path x x, contractibleBasisLoopCode.Realizes code p } →
        FundamentalGroup X x := fun code ↦
          FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (Classical.choose code.2))
  have hF : Function.Surjective F := by
    -- Every loop is homotopic to one realized by a dense-marker code from the countable basis.
    exact surjectiveRealizableContractibleBasisLoopCode (X := X) (b := b) (d := d)
      hbBasis hbContractible hdDense x
  let _ : Countable
      { code : contractibleBasisLoopCode (X := X) (b := b) d //
        ∃ p : Path x x, contractibleBasisLoopCode.Realizes code p } := hCodeCountable
  exact hF.countable

/-- Clause (9) of Proposition 1.40: the fundamental group at any basepoint of a topological
manifold with boundary is countable. -/
theorem countable_fundamentalGroup (x : M) : Countable (FundamentalGroup M x) := by
  letI : LocPathConnectedSpace M :=
    topologicalManifoldWithBoundary_locPathConnectedSpace (n := n) (M := M)
  obtain ⟨b, hbCountable, hbBasis⟩ :=
    exists_countable_precompact_coordinate_ball_half_ball_basis (n := n) (M := M)
  -- The remaining work is the abstract closing theorem for countable contractible bases.
  refine countable_fundamentalGroup_of_countable_contractible_basis (x := x) hbCountable
    hbBasis.isTopologicalBasis ?_
  intro s hs
  rcases hbBasis.mem_isPrecompactBoundaryModelCoordinateBall_or_halfBall s hs with hsBall | hsHalf
  · exact contractibleSpace_of_boundaryModelCoordinateBallOrHalfBall
      (M := M) (n := n) (s := s) (Or.inl hsBall.1)
  · exact contractibleSpace_of_boundaryModelCoordinateBallOrHalfBall
      (M := M) (n := n) (s := s) (Or.inr hsHalf.1)

end
