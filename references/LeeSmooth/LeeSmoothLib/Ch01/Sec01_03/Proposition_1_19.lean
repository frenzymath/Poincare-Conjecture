import LeeSmoothLib.Ch01.Sec01_03.Definition_1_3_extra_1
-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search note: `lean_leansearch` was unavailable here.
-- Local repo search reused `IsRegularCoordinateBall` from Definition 1.3-extra-1.

open Set TopologicalSpace
open scoped Manifold

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [T2Space M] [SecondCountableTopology M]
variable [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]

-- Proof sketch: start from the countable basis of precompact coordinate balls from Lemma 1.10 and,
-- inside each chosen chart, translate and rescale the Euclidean ball so that the given basis
-- element becomes a concentric ball with compact closure contained in a larger chart ball.
/-- A set of subsets of a manifold that is a countable topological basis consisting of regular
coordinate balls. -/
class IsCountableRegularCoordinateBallBasis (b : Set (Set M)) : Prop where
  countable : b.Countable
  isTopologicalBasis : IsTopologicalBasis b
  regular : ∀ s ∈ b, IsRegularCoordinateBall (EuclideanSpace ℝ (Fin n)) s

/-- Helper for Proposition 1.19: Euclidean translations belong to the smooth model-space
groupoid. -/
private theorem euclideanTranslation_mem_contDiffGroupoid
    (v : EuclideanSpace ℝ (Fin n)) :
    (Homeomorph.addRight v).toOpenPartialHomeomorph ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) := by
  -- Both the translation and its inverse are smooth on all of Euclidean space.
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  constructor
  · simpa [modelWithCornersSelf_coe, Homeomorph.addRight] using
      (contDiff_id.add contDiff_const).contDiffOn
  · simpa [modelWithCornersSelf_coe, Homeomorph.addRight] using
      (contDiff_id.add contDiff_const).contDiffOn

/-- Helper for Proposition 1.19: postcomposing a maximal-atlas chart with a smooth model-space
chart change keeps it in the maximal atlas. -/
private theorem trans_mem_maximalAtlas_of_mem_groupoid
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M)
    {chi : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (hchi : chi ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n)) :
    e.trans chi ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M := by
  -- Maximal-atlas membership is checked by compatibility with the original atlas charts.
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e' he'
  have he'max : e' ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M := by
    exact IsManifold.subset_maximalAtlas he'
  have hleft : e.symm.trans e' ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) := by
    exact IsManifold.compatible_of_mem_maximalAtlas he he'max
  have hright : e'.symm.trans e ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) := by
    exact IsManifold.compatible_of_mem_maximalAtlas he'max he
  constructor
  · -- The left transition adds the smooth model-space change on the right.
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n)).trans
      ((contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n)).symm hchi) hleft
  · -- The right transition is the old transition followed by the new smooth change.
    have hright' : (e'.symm.trans e).trans chi ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) := by
      exact (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n)).trans hright hchi
    simpa [OpenPartialHomeomorph.trans_assoc] using hright'

/-- Helper for Proposition 1.19: centering a maximal-atlas chart at a source point keeps it in the
maximal atlas. -/
private theorem centeredChart_mem_maximalAtlas
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M) (p : e.source) :
    e.centerAt p ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M := by
  -- `centerAt` is just postcomposition with a Euclidean translation.
  rw [OpenPartialHomeomorph.centerAt, OpenPartialHomeomorph.transHomeomorph_eq_trans]
  exact trans_mem_maximalAtlas_of_mem_groupoid he
    (euclideanTranslation_mem_contDiffGroupoid (-e p))

/-- Helper for Proposition 1.19: pulling back a smaller concentric Euclidean ball through a chart
whose target is a larger concentric Euclidean ball produces a regular coordinate ball. -/
private theorem isRegularCoordinateBall_chart_preimage_metric_ball
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (htarget : e.target = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) :
    IsRegularCoordinateBall (EuclideanSpace ℝ (Fin n))
      (e.symm '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) := by
  let s : Set M := e.symm '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
  let t : Set M := e.symm '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r
  have hsmall_target : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ e.target := by
    rw [htarget]
    exact Metric.ball_subset_ball (le_of_lt hrR)
  have hclosed_target : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r ⊆ e.target := by
    rw [htarget]
    exact Metric.closedBall_subset_ball hrR
  have hs_subset_t : s ⊆ t := by
    exact Set.image_mono (Metric.ball_subset_closedBall : _)
  have ht_closed : IsClosed t := by
    -- The closed Euclidean ball is compact, and its pullback by the inverse chart stays compact.
    have ht_compact : IsCompact t := by
      exact (isCompact_closedBall
        (x := (0 : EuclideanSpace ℝ (Fin n))) (r := r)).image_of_continuousOn
          (e.continuousOn_symm.mono hclosed_target)
    exact ht_compact.isClosed
  have hclosure_subset : closure s ⊆ t := by
    -- The closure lies in the closed pullback because that pullback is closed and contains `s`.
    exact closure_minimal hs_subset_t ht_closed
  have ht_subset_closure : t ⊆ closure s := by
    -- The inverse chart sends the closure of the small Euclidean ball into the closure of its
    -- pullback.
    have hcont : ContinuousOn e.symm (closure (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)) := by
      rw [closure_ball (0 : EuclideanSpace ℝ (Fin n)) hr.ne']
      exact e.continuousOn_symm.mono hclosed_target
    have himage :
        e.symm '' closure (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) ⊆ closure s := by
      simpa [s] using hcont.image_closure (s := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)
    rw [closure_ball (0 : EuclideanSpace ℝ (Fin n)) hr.ne'] at himage
    simpa [t] using himage
  have hclosure_eq : closure s = t := by
    exact Subset.antisymm hclosure_subset ht_subset_closure
  have ht_subset_source : t ⊆ e.source := by
    rw [show t = e.symm '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r by rfl,
      e.symm_image_eq_source_inter_preimage hclosed_target]
    exact inter_subset_left
  refine ⟨e, he, ?_, r, R, hr, hrR, ?_, ?_, htarget⟩
  · -- The closure stays inside the chart source because the closed Euclidean ball stays in target.
    exact hclosure_subset.trans ht_subset_source
  · -- The chart sends the pulled-back small ball back to that Euclidean ball.
    simpa [s] using e.image_symm_image_of_subset_target hsmall_target
  · -- After identifying the closure, the chart sends it to the closed Euclidean ball.
    calc
      e '' closure s = e '' t := by rw [hclosure_eq]
      _ = Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r := by
        simpa [t] using e.image_symm_image_of_subset_target hclosed_target

/-- Helper for Proposition 1.19: regular coordinate balls are open. -/
private theorem IsRegularCoordinateBall.isOpen {s : Set M}
    (hs : IsRegularCoordinateBall (EuclideanSpace ℝ (Fin n)) s) : IsOpen s := by
  rcases hs with ⟨chart, -, hclosure, r, r', hr, hr', hsImage, -, -⟩
  have hs_subset_source : s ⊆ chart.source := by
    exact subset_trans subset_closure hclosure
  -- The chart image is an open Euclidean ball, so openness transports back along the chart.
  have himage_open : IsOpen (chart '' s) := by
    simpa [hsImage] using Metric.isOpen_ball
  exact (chart.isOpen_image_iff_of_subset_source hs_subset_source).1 himage_open

/-- Helper for Proposition 1.19: every point of an open set lies in a regular coordinate ball
contained in that open set. -/
private theorem exists_isRegularCoordinateBall_subset_of_mem_open {x : M} {u : Set M}
    (hx : x ∈ u) (hu : IsOpen u) :
    ∃ s : Set M, IsRegularCoordinateBall (EuclideanSpace ℝ (Fin n)) s ∧ x ∈ s ∧ s ⊆ u := by
  let rawChart := chartAt (EuclideanSpace ℝ (Fin n)) x
  let px : rawChart.source := ⟨x, mem_chart_source (EuclideanSpace ℝ (Fin n)) x⟩
  let e := rawChart.centerAt px
  let w : Set (EuclideanSpace ℝ (Fin n)) := e '' (e.source ∩ u)
  have he : e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M := by
    -- Centering the preferred chart preserves maximal-atlas membership.
    exact centeredChart_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡 n) (n := (⊤ : WithTop ℕ∞)) x) px
  have hzero_w : (0 : EuclideanSpace ℝ (Fin n)) ∈ w := by
    -- The centered chart sends `x` to `0`, and `x` belongs to the chosen open set.
    refine ⟨x, ⟨(e.centerAt_isCenteredAt px).1, hx⟩, ?_⟩
    simpa [e] using (rawChart.centerAt_isCenteredAt px).2
  have hw_open : IsOpen w := by
    -- The chart image of the neighborhood inside its source is open in Euclidean space.
    simpa [w] using e.isOpen_image_source_inter hu
  obtain ⟨R, hRpos, hclosed⟩ :
      ∃ R : ℝ, 0 < R ∧ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ w := by
    -- Choose a small closed Euclidean ball around `0` inside the chart image of `u`.
    exact Metric.nhds_basis_closedBall.mem_iff.1 (hw_open.mem_nhds hzero_w)
  have hw_target : w ⊆ e.target := by
    -- Images of subsets of the source stay inside the chart target.
    simpa [w] using
      (Set.image_mono (show e.source ∩ u ⊆ e.source from inter_subset_left)).trans
        e.image_source_eq_target.subset
  have hball_target : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R ⊆ e.target := by
    exact (Metric.ball_subset_closedBall : _).trans (hclosed.trans hw_target)
  let eR :=
    e.trans (OpenPartialHomeomorph.ofSet
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) Metric.isOpen_ball)
  have heR : eR ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M := by
    -- Restricting the target to an open Euclidean ball preserves maximal-atlas membership.
    exact trans_mem_maximalAtlas_of_mem_groupoid he
      (ofSet_mem_contDiffGroupoid (I := 𝓡 n)
        (n := (⊤ : WithTop ℕ∞)) Metric.isOpen_ball)
  have hsourceR :
      eR.source = e.symm '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := by
    -- The restricted chart is defined exactly on the pullback of the chosen larger ball.
    exact (e.symm_image_eq_source_inter_preimage hball_target).symm
  have htargetR : eR.target = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := by
    -- The target side becomes precisely the chosen Euclidean ball.
    dsimp [eR]
    exact inter_eq_left.2 hball_target
  let r : ℝ := R / 2
  have hr : 0 < r := by
    -- Halving the positive radius still gives a positive radius.
    dsimp [r]
    linarith
  have hrR : r < R := by
    -- The halved radius is strictly smaller than the original one.
    dsimp [r]
    linarith
  let s : Set M := eR.symm '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
  have hsmall_subset_big :
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := by
    exact Metric.ball_subset_ball (le_of_lt hrR)
  have hs_eq : s = e.symm '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := by
    -- Restricting first to the big ball and then to the small ball is the same as restricting
    -- directly to the small ball.
    have htrans :
        eR.trans (OpenPartialHomeomorph.ofSet
            (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) Metric.isOpen_ball) =
          e.trans (OpenPartialHomeomorph.ofSet
            (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) Metric.isOpen_ball) := by
      dsimp [eR]
      have hOfSet :
          (OpenPartialHomeomorph.ofSet
              (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) Metric.isOpen_ball).trans
            (OpenPartialHomeomorph.ofSet
              (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) Metric.isOpen_ball) =
            OpenPartialHomeomorph.ofSet
              (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) Metric.isOpen_ball := by
        rw [OpenPartialHomeomorph.ofSet_trans_ofSet]
        congr
        ext z
        simp [Set.inter_eq_right.mpr hsmall_subset_big]
      simpa [OpenPartialHomeomorph.trans_assoc, hOfSet]
    have hsourceLeft :
        (eR.trans (OpenPartialHomeomorph.ofSet
            (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) Metric.isOpen_ball)).source =
          s := by
      exact (eR.symm_image_eq_source_inter_preimage
        (by simpa [htargetR] using hsmall_subset_big)).symm
    have hsourceRight :
        (e.trans (OpenPartialHomeomorph.ofSet
            (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) Metric.isOpen_ball)).source =
          e.symm '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := by
      exact (e.symm_image_eq_source_inter_preimage (hsmall_subset_big.trans hball_target)).symm
    exact hsourceLeft.symm.trans ((congrArg (fun f => f.source) htrans).trans hsourceRight)
  have hs_regular : IsRegularCoordinateBall (EuclideanSpace ℝ (Fin n)) s := by
    -- The restricted centered chart witnesses the regularity of the pulled-back smaller ball.
    exact isRegularCoordinateBall_chart_preimage_metric_ball eR heR hr hrR htargetR
  have hxs : x ∈ s := by
    -- The centered chart sends `x` to `0`, so `x` lies in every positive-radius centered ball.
    refine hs_eq.symm ▸ ?_
    refine ⟨0, Metric.mem_ball_self hr, ?_⟩
    have hcentered : e x = 0 := by
      simpa [e] using (rawChart.centerAt_isCenteredAt px).2
    simpa [hcentered] using e.left_inv (show x ∈ e.source from (e.centerAt_isCenteredAt px).1)
  have hs_subset_u : s ⊆ u := by
    -- The pulled-back smaller ball sits inside the chosen neighborhood because its image does.
    refine hs_eq.symm ▸ ?_
    have hball_w : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ w := by
      exact hsmall_subset_big.trans (Metric.ball_subset_closedBall.trans hclosed)
    have hs_subset_source_u : e.symm '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆
        e.source ∩ u := by
      refine (Set.image_mono hball_w).trans ?_
      have himage : e.symm '' w = e.source ∩ u := by
        simpa [w] using e.symm_image_image_of_subset_source
          (s := e.source ∩ u) (show e.source ∩ u ⊆ e.source from inter_subset_left)
      exact himage.subset
    exact fun y hy ↦ (hs_subset_source_u hy).2
  exact ⟨s, hs_regular, hxs, hs_subset_u⟩

/-- Helper for Proposition 1.19: regular coordinate balls form a topological basis. -/
private theorem isTopologicalBasis_isRegularCoordinateBall :
    IsTopologicalBasis { s : Set M |
      IsRegularCoordinateBall (EuclideanSpace ℝ (Fin n)) s } := by
  -- The local regular-ball construction supplies a basis element in every open neighborhood.
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro s hs
    exact hs.isOpen
  · intro x u hx hu
    obtain ⟨s, hs, hxs, hsu⟩ :=
      exists_isRegularCoordinateBall_subset_of_mem_open (n := n) (M := M) hx hu
    exact ⟨s, hs, hxs, hsu⟩

/-- Proposition 1.19: every smooth manifold has a countable basis of regular coordinate balls. -/
theorem exists_countable_regular_coordinate_ball_basis :
    ∃ b : Set (Set M), @IsCountableRegularCoordinateBallBasis n M _ _ _ b := by
  classical
  let B : Set (Set M) := { s : Set M | IsRegularCoordinateBall (EuclideanSpace ℝ (Fin n)) s }
  have hB : IsTopologicalBasis B :=
    isTopologicalBasis_isRegularCoordinateBall (n := n) (M := M)
  -- Once the full regular-ball basis is available, second countability thins it to a countable
  -- subbasis.
  obtain ⟨b, hbB, hbCountable, hbBasis⟩ := hB.exists_countable
  exact ⟨b, ⟨hbCountable, hbBasis, fun s hs ↦ hbB hs⟩⟩
