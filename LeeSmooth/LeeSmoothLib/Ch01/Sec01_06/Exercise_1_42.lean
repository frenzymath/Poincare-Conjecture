import LeeSmoothLib.Ch01.Sec01_05.Proposition_1_40
import LeeSmoothLib.Ch01.Sec01_06.Definition_1_6_extra_2
import LeeSmoothLib.Ch01.Sec01_06.Definition_1_6_extra_3
-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search note: no directly relevant mathlib theorem surfaced here; this item follows the
-- local boundary-manifold owners from Definition 1.6-extra-2 and Proposition 1.40.
-- This exercise now reuses the earlier chapter owner `IsRegularCoordinateHalfBall` directly and
-- relates the new ball/half-ball statements to the boundary-model coordinate-ball API of
-- Proposition 1.40 instead of maintaining a parallel local vocabulary.

universe u

open Set
open scoped Manifold

variable {n : ℕ}
variable {M : Type u} [TopologicalSpace M]

section PositiveDim

variable [NeZero n]
variable [ChartedSpace (EuclideanHalfSpace n) M]
variable [IsManifold (𝓡∂ n) (⊤ : WithTop ℕ∞) M]

/-- A regular coordinate ball is a subset whose closure lies in the source of a smooth boundary
chart sending the subset to an open Euclidean ball, its closure to the corresponding closed ball,
and the whole chart source to a larger open Euclidean ball centered away from the boundary
hyperplane. This is the ball analogue of Definition 1.6-extra-3's regular coordinate half-balls.
The ambient dimension `n` is explicit because it is not recoverable from `s : Set M` alone. -/
def IsRegularCoordinateBall (n : ℕ) [NeZero n] {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : WithTop ℕ∞) M] (s : Set M) : Prop :=
  ∃ chart : OpenPartialHomeomorph M (EuclideanHalfSpace n),
    chart ∈ IsManifold.maximalAtlas (𝓡∂ n) (⊤ : WithTop ℕ∞) M ∧
      closure s ⊆ chart.source ∧
        ∃ c : EuclideanHalfSpace n, ∃ outerRadius innerRadius : ℝ,
          0 < innerRadius ∧
          innerRadius < outerRadius ∧
          outerRadius < c.1 0 ∧
          chart '' s = Metric.ball c innerRadius ∧
          chart '' closure s = Metric.closedBall c innerRadius ∧
          chart.target = Metric.ball c outerRadius

/-- A regular coordinate ball yields a boundary-model coordinate ball after restricting the witness
chart to the smaller ball. -/
theorem IsRegularCoordinateBall.isBoundaryModelCoordinateBall {s : Set M}
    (hs : IsRegularCoordinateBall n s) :
    IsBoundaryModelCoordinateBall n s := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rcases hs with
    ⟨chart, hchart, hclosure, c, outerRadius, innerRadius, hInnerPos, hInnerOuter, hOuterCenter,
      hImage, _, hTarget⟩
  let e :=
    chart.trans (OpenPartialHomeomorph.ofSet (Metric.ball c innerRadius) Metric.isOpen_ball)
  have hs_subset_source : s ⊆ chart.source := subset_trans subset_closure hclosure
  have hball_target : Metric.ball c innerRadius ⊆ chart.target := by
    rw [hTarget]
    exact Metric.ball_subset_ball (le_of_lt hInnerOuter)
  have hsource : e.source = s := by
    -- The restricted chart is defined exactly on the inverse image of the smaller ball.
    calc
      e.source = chart.symm '' Metric.ball c innerRadius := by
        exact (chart.symm_image_eq_source_inter_preimage hball_target).symm
      _ = s := by
        ext z
        constructor
        · intro hz
          rcases hz with ⟨y, hyBall, rfl⟩
          have hyImage : y ∈ chart '' s := by
            simpa [hImage] using hyBall
          rcases hyImage with ⟨w, hw, hwy⟩
          rw [← hwy, chart.left_inv (hs_subset_source hw)]
          exact hw
        · intro hz
          refine ⟨chart z, ?_, chart.left_inv (hs_subset_source hz)⟩
          rw [← hImage]
          exact ⟨z, hz, rfl⟩
  refine ⟨e, hsource, c, innerRadius, hInnerPos, ?_, ?_⟩
  · exact lt_trans hInnerOuter hOuterCenter
  · -- On the target side, restricting to the smaller half-space ball leaves exactly that ball.
    dsimp [e]
    exact inter_eq_left.2 hball_target

/-- A regular coordinate half-ball yields a boundary-model coordinate half-ball after restricting
its witnessing chart to the smaller half-ball. -/
theorem IsRegularCoordinateHalfBall.isBoundaryModelCoordinateHalfBall {s : Set M}
    (hs : IsRegularCoordinateHalfBall n s) :
    IsBoundaryModelCoordinateHalfBall n s := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rcases hs with
    ⟨chart, hchart, hclosure, outerRadius, innerRadius, hInnerPos, hInnerOuter, hImage, _,
      hTarget⟩
  let e :=
    chart.trans (OpenPartialHomeomorph.ofSet
      (Metric.ball (0 : EuclideanHalfSpace (m + 1)) innerRadius) Metric.isOpen_ball)
  have hs_subset_source : s ⊆ chart.source := subset_trans subset_closure hclosure
  have hball_target :
      Metric.ball (0 : EuclideanHalfSpace (m + 1)) innerRadius ⊆ chart.target := by
    rw [hTarget]
    exact Metric.ball_subset_ball (le_of_lt hInnerOuter)
  have hsource :
      e.source = s := by
    calc
      e.source =
          chart.symm '' Metric.ball (0 : EuclideanHalfSpace (m + 1)) innerRadius := by
        -- The restriction source is the inverse image of the smaller half-space ball.
        exact chart.symm_image_eq_source_inter_preimage hball_target |>.symm
      _ = s := by
        -- The regular-half-ball image formula identifies `s` with that inverse image.
        ext z
        constructor
        · intro hz
          rcases hz with ⟨y, hyBall, rfl⟩
          have hyImage : y ∈ chart '' s := by
            simpa [hImage] using hyBall
          rcases hyImage with ⟨w, hw, hwy⟩
          rw [← hwy, chart.left_inv (hs_subset_source hw)]
          exact hw
        · intro hz
          refine ⟨chart z, ?_, chart.left_inv (hs_subset_source hz)⟩
          rw [← hImage]
          exact ⟨z, hz, rfl⟩
  refine ⟨e, hsource, (0 : EuclideanHalfSpace (m + 1)), innerRadius, hInnerPos, rfl, ?_⟩
  dsimp [e]
  exact inter_eq_left.2 hball_target

/-- Every regular coordinate ball is open. -/
theorem IsRegularCoordinateBall.isOpen {s : Set M} (hs : IsRegularCoordinateBall n s) :
    IsOpen s := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rcases (hs.isBoundaryModelCoordinateBall :
      IsBoundaryModelCoordinateBall (m + 1) s) with
    ⟨chart, rfl, c, r, hr, _hc, _htarget⟩
  -- The boundary-model bridge turns openness into the standard `open_source` fact for charts.
  simpa using chart.open_source

/-- Every regular coordinate half-ball is open. -/
theorem IsRegularCoordinateHalfBall.isOpen {s : Set M}
    (hs : IsRegularCoordinateHalfBall n s) :
    IsOpen s := by
  -- Restrict the witnessing chart to the inner half-ball, then reuse openness of the source.
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rcases (hs.isBoundaryModelCoordinateHalfBall :
      IsBoundaryModelCoordinateHalfBall (m + 1) s) with
    ⟨chart, rfl, c, r, hr, _hc, htarget⟩
  simpa using chart.open_source

/-- Helper for Exercise 1.42: closed metric balls in the Euclidean half-space are compact. -/
private theorem isCompact_closedBall_euclideanHalfSpace
    (c : EuclideanHalfSpace n) (r : ℝ) :
    IsCompact (Metric.closedBall c r : Set (EuclideanHalfSpace n)) := by
  -- Compare the half-space closed ball with the ambient Euclidean closed ball via the closed
  -- subtype embedding.
  have hcoord :
      Continuous fun x : EuclideanSpace ℝ (Fin n) ↦ x 0 := by
    exact PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) 0
  have hclosedHalf :
      IsClosed { x : EuclideanSpace ℝ (Fin n) | 0 ≤ x 0 } := by
    exact isClosed_le continuous_const hcoord
  have hambient : IsCompact (Metric.closedBall c.1 r) :=
    isCompact_closedBall c.1 r
  simpa [Metric.closedBall, Subtype.dist_eq] using
    hclosedHalf.isClosedEmbedding_subtypeVal.isCompact_preimage hambient

/-- Helper for Exercise 1.42: the closure of a zero-centered open half-space ball is the
corresponding closed half-space ball. -/
private theorem closure_ball_zero_euclideanHalfSpace {r : ℝ} (hr : 0 < r) :
    closure (Metric.ball (0 : EuclideanHalfSpace n) r) =
      Metric.closedBall (0 : EuclideanHalfSpace n) r := by
  refine Subset.antisymm Metric.closure_ball_subset_closedBall ?_
  intro x hx
  by_cases hxr : dist x (0 : EuclideanHalfSpace n) < r
  · -- Interior points already lie in the open ball, hence in its closure.
    exact subset_closure (Metric.mem_ball.2 hxr)
  · -- Boundary points are approximated by scaling slightly toward the origin.
    rw [Metric.mem_closedBall] at hx
    have hxeq : dist x (0 : EuclideanHalfSpace n) = r := le_antisymm hx (not_lt.1 hxr)
    have hxnorm : ‖x.1‖ = r := by
      have hxnormEq : ‖x.1‖ = dist x (0 : EuclideanHalfSpace n) := by
        change ‖x.1‖ = dist x.1 (0 : EuclideanSpace ℝ (Fin n))
        simpa [dist_eq_norm]
      exact hxnormEq.trans hxeq
    exact Metric.mem_closure_iff.2 <| by
      intro ε hε
      let δ : ℝ := min (ε / (2 * r)) (1 / 2)
      have hδpos : 0 < δ := by
        dsimp [δ]
        refine lt_min ?_ (by norm_num)
        exact div_pos hε (by positivity)
      have hδleHalf : δ ≤ 1 / 2 := by
        exact min_le_right _ _
      have hδle : δ ≤ ε / (2 * r) := by
        exact min_le_left _ _
      have hδnonneg : 0 ≤ δ := le_of_lt hδpos
      have hδleHalf : δ ≤ 1 / 2 := by
        exact min_le_right _ _
      have hOneSub_nonneg : 0 ≤ 1 - δ := by
        have : δ ≤ 1 := by linarith
        linarith
      have hOneSub_lt_one : 1 - δ < 1 := by
        linarith
      let y : EuclideanHalfSpace n := ⟨(1 - δ) • x.1, by
        simpa [Pi.smul_apply] using mul_nonneg hOneSub_nonneg x.2⟩
      have hy_mem : y ∈ Metric.ball (0 : EuclideanHalfSpace n) r := by
        -- Shrinking by a factor strictly less than `1` moves the point into the open ball.
        refine Metric.mem_ball.2 ?_
        change dist ((1 - δ) • x.1) (0 : EuclideanSpace ℝ (Fin n)) < r
        calc
          dist ((1 - δ) • x.1) (0 : EuclideanSpace ℝ (Fin n)) = ‖(1 - δ) • x.1‖ := by
            simpa [dist_eq_norm]
          _ = |1 - δ| * ‖x.1‖ := norm_smul _ _
          _ = (1 - δ) * r := by rw [abs_of_nonneg hOneSub_nonneg, hxnorm]
          _ < r := by
            simpa using mul_lt_mul_of_pos_right hOneSub_lt_one hr
      have hδr_le : δ * r ≤ ε / 2 := by
        have hmul := mul_le_mul_of_nonneg_right hδle (le_of_lt hr)
        calc
          δ * r ≤ (ε / (2 * r)) * r := hmul
          _ = ε / 2 := by
            field_simp [hr.ne']
      have hdist :
          dist x y < ε := by
        -- The scaled point stays arbitrarily close to the original boundary point.
        have hsub : x.1 - (1 - δ) • x.1 = δ • x.1 := by
          ext i
          simp [sub_eq_add_neg, δ]
          ring
        change dist x.1 ((1 - δ) • x.1) < ε
        calc
          dist x.1 ((1 - δ) • x.1) = ‖x.1 - (1 - δ) • x.1‖ := by
            simpa [dist_eq_norm]
          _ = ‖δ • x.1‖ := by rw [hsub]
          _ = |δ| * ‖x.1‖ := norm_smul _ _
          _ = δ * r := by rw [abs_of_nonneg hδnonneg, hxnorm]
          _ ≤ ε / 2 := hδr_le
          _ < ε := by linarith
      exact ⟨y, hy_mem, hdist⟩

/-- Helper for Exercise 1.42: every open metric ball in the Euclidean half-space has closure equal
to the corresponding closed metric ball. -/
private theorem closure_ball_euclideanHalfSpace {c : EuclideanHalfSpace n} {r : ℝ} (hr : 0 < r) :
    closure (Metric.ball c r) = Metric.closedBall c r := by
  refine Subset.antisymm Metric.closure_ball_subset_closedBall ?_
  intro x hx
  by_cases hxr : dist x c < r
  · -- Interior points already lie in the open ball, hence in its closure.
    exact subset_closure (Metric.mem_ball.2 hxr)
  · -- Boundary points are approximated by moving slightly toward the center along the segment.
    rw [Metric.mem_closedBall] at hx
    have hxeq : dist x c = r := le_antisymm hx (not_lt.1 hxr)
    exact Metric.mem_closure_iff.2 <| by
      intro ε hε
      let δ : ℝ := min (ε / (2 * r)) (1 / 2)
      have hδpos : 0 < δ := by
        dsimp [δ]
        refine lt_min ?_ (by norm_num)
        exact div_pos hε (by positivity)
      have hδle : δ ≤ ε / (2 * r) := by
        exact min_le_left _ _
      have hδnonneg : 0 ≤ δ := le_of_lt hδpos
      have hδlt_one : δ < 1 := by
        exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hOneSub_nonneg : 0 ≤ 1 - δ := by
        linarith
      have hOneSub_lt_one : 1 - δ < 1 := by
        linarith
      have hnormxc : ‖x.1 - c.1‖ = dist x c := by
        change ‖x.1 - c.1‖ = dist x.1 c.1
        simp [dist_eq_norm]
      let y : EuclideanHalfSpace n := ⟨(1 - δ) • x.1 + δ • c.1, by
        simpa [Pi.add_apply, Pi.smul_apply] using
          add_nonneg (mul_nonneg hOneSub_nonneg x.2) (mul_nonneg hδnonneg c.2)⟩
      have hy_mem : y ∈ Metric.ball c r := by
        -- Contracting the vector from `c` to `x` moves the point into the open ball.
        have hsegment :
            ((1 - δ) • x.1 + δ • c.1) - c.1 = (1 - δ) • (x.1 - c.1) := by
          ext i
          simp [Pi.add_apply, Pi.smul_apply, sub_eq_add_neg]
          ring
        refine Metric.mem_ball.2 ?_
        change dist ((1 - δ) • x.1 + δ • c.1) c.1 < r
        calc
          dist ((1 - δ) • x.1 + δ • c.1) c.1 = ‖((1 - δ) • x.1 + δ • c.1) - c.1‖ := by
            simp [dist_eq_norm]
          _ = ‖(1 - δ) • (x.1 - c.1)‖ := by rw [hsegment]
          _ = |1 - δ| * ‖x.1 - c.1‖ := norm_smul _ _
          _ = (1 - δ) * dist x c := by
            rw [abs_of_nonneg hOneSub_nonneg, hnormxc]
          _ = (1 - δ) * r := by rw [hxeq]
          _ < r := by
            simpa using mul_lt_mul_of_pos_right hOneSub_lt_one hr
      have hδr_le : δ * r ≤ ε / 2 := by
        have hmul := mul_le_mul_of_nonneg_right hδle (le_of_lt hr)
        have hhalf : (ε / (2 * r)) * r = ε / 2 := by
          field_simp [hr.ne']
        calc
          δ * r ≤ (ε / (2 * r)) * r := hmul
          _ = ε / 2 := hhalf
      have hdist : dist x y < ε := by
        -- The contracted point stays arbitrarily close to the original boundary point.
        have hcontract :
            x.1 - ((1 - δ) • x.1 + δ • c.1) = δ • (x.1 - c.1) := by
          ext i
          simp [Pi.add_apply, Pi.smul_apply, sub_eq_add_neg]
          ring
        change dist x.1 ((1 - δ) • x.1 + δ • c.1) < ε
        calc
          dist x.1 ((1 - δ) • x.1 + δ • c.1) = ‖x.1 - ((1 - δ) • x.1 + δ • c.1)‖ := by
            simp [dist_eq_norm]
          _ = ‖δ • (x.1 - c.1)‖ := by rw [hcontract]
          _ = |δ| * ‖x.1 - c.1‖ := norm_smul _ _
          _ = δ * dist x c := by
            rw [abs_of_nonneg hδnonneg, hnormxc]
          _ = δ * r := by rw [hxeq]
          _ ≤ ε / 2 := hδr_le
          _ < ε := by linarith
      exact ⟨y, hy_mem, hdist⟩

/-- Helper for Exercise 1.42: a maximal-atlas chart whose target is a larger half-space ball
centered at `0` makes the smaller concentric preimage into a regular coordinate half-ball. -/
private theorem isRegularCoordinateHalfBall_zeroCenteredChartPreimageMetricBall
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    [T2Space M]
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ n) (⊤ : WithTop ℕ∞) M)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (htarget : e.target = Metric.ball (0 : EuclideanHalfSpace n) R) :
    IsRegularCoordinateHalfBall n
      (e.symm '' Metric.ball (0 : EuclideanHalfSpace n) r) := by
  let s : Set M := e.symm '' Metric.ball (0 : EuclideanHalfSpace n) r
  let t : Set M := e.symm '' Metric.closedBall (0 : EuclideanHalfSpace n) r
  have hsmall_target : Metric.ball (0 : EuclideanHalfSpace n) r ⊆ e.target := by
    -- The smaller open half-ball lies inside the larger chart target.
    rw [htarget]
    exact Metric.ball_subset_ball (le_of_lt hrR)
  have hclosed_target : Metric.closedBall (0 : EuclideanHalfSpace n) r ⊆ e.target := by
    -- The corresponding closed half-ball is still compactly contained in the larger target ball.
    rw [htarget]
    exact Metric.closedBall_subset_ball hrR
  have hs_subset_t : s ⊆ t := by
    -- Passing from the open half-ball to the closed half-ball only enlarges the pullback.
    exact Set.image_mono (Metric.ball_subset_closedBall : _)
  have ht_closed : IsClosed t := by
    -- The pullback of the compact closed half-ball is compact, hence closed in the Hausdorff
    -- ambient manifold.
    have ht_compact : IsCompact t := by
      exact
        (isCompact_closedBall_euclideanHalfSpace (0 : EuclideanHalfSpace n) r).image_of_continuousOn
          (e.continuousOn_symm.mono hclosed_target)
    exact ht_compact.isClosed
  have hclosure_subset : closure s ⊆ t := by
    -- The closed pullback contains the small pullback, so it contains its closure.
    exact closure_minimal hs_subset_t ht_closed
  have ht_subset_source : t ⊆ e.source := by
    -- The closed pullback stays in the chart source because the closed half-ball stays in target.
    rw [show t = e.symm '' Metric.closedBall (0 : EuclideanHalfSpace n) r by rfl,
      e.symm_image_eq_source_inter_preimage hclosed_target]
    exact inter_subset_left
  have ht_subset_closure : t ⊆ closure s := by
    -- The inverse chart sends the closure of the small half-space ball into the closure of its
    -- pullback.
    have hcont : ContinuousOn e.symm (closure (Metric.ball (0 : EuclideanHalfSpace n) r)) := by
      rw [closure_ball_zero_euclideanHalfSpace hr]
      exact e.continuousOn_symm.mono hclosed_target
    have himage :
        e.symm '' closure (Metric.ball (0 : EuclideanHalfSpace n) r) ⊆ closure s := by
      simpa [s] using
        (show e.symm '' closure (Metric.ball (0 : EuclideanHalfSpace n) r) ⊆
            closure (e.symm '' Metric.ball (0 : EuclideanHalfSpace n) r) from
          hcont.image_closure)
    rw [closure_ball_zero_euclideanHalfSpace hr] at himage
    simpa [t] using himage
  have hclosure_eq : closure s = t := by
    exact Subset.antisymm hclosure_subset ht_subset_closure
  refine ⟨e, he, ?_, R, r, hr, hrR, ?_, ?_, htarget⟩
  · -- The closure stays in the chart source because the closed pullback stays there.
    exact hclosure_subset.trans ht_subset_source
  · -- The chart sends the pulled-back small half-ball back to that model half-ball.
    simpa [s] using e.image_symm_image_of_subset_target hsmall_target
  · -- After identifying the closure, the chart sends it to the closed model half-ball.
    calc
      e '' closure s = e '' t := by rw [hclosure_eq]
      _ = Metric.closedBall (0 : EuclideanHalfSpace n) r := by
        simpa [t] using e.image_symm_image_of_subset_target hclosed_target

/-- Helper for Exercise 1.42: postcomposing a maximal-atlas chart with a smooth half-space model
chart change keeps it in the maximal atlas. -/
private theorem trans_mem_maximalAtlas_of_mem_groupoid
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ n) (⊤ : WithTop ℕ∞) M)
    {chi : OpenPartialHomeomorph (EuclideanHalfSpace n) (EuclideanHalfSpace n)}
    (hchi : chi ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡∂ n)) :
    e.trans chi ∈ IsManifold.maximalAtlas (𝓡∂ n) (⊤ : WithTop ℕ∞) M := by
  -- Maximal-atlas membership is tested by compatibility with the original atlas charts.
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e' he'
  have he'max : e' ∈ IsManifold.maximalAtlas (𝓡∂ n) (⊤ : WithTop ℕ∞) M := by
    exact IsManifold.subset_maximalAtlas he'
  have hleft : e.symm.trans e' ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡∂ n) := by
    exact IsManifold.compatible_of_mem_maximalAtlas he he'max
  have hright : e'.symm.trans e ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡∂ n) := by
    exact IsManifold.compatible_of_mem_maximalAtlas he'max he
  constructor
  · -- The left transition adds the smooth model-space change on the right.
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡∂ n)).trans
      ((contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡∂ n)).symm hchi) hleft
  · -- The right transition is the old one followed by the new smooth model change.
    have hright' :
        (e'.symm.trans e).trans chi ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡∂ n) := by
      exact (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡∂ n)).trans hright hchi
    simpa [OpenPartialHomeomorph.trans_assoc] using hright'

/-- Helper for Exercise 1.42: translation by a vector tangent to the boundary hyperplane defines a
homeomorphism of the model half-space. -/
private noncomputable def boundaryParallelTranslationHomeomorph
    (c : EuclideanHalfSpace n) (hc : c.1 0 = 0) :
    EuclideanHalfSpace n ≃ₜ EuclideanHalfSpace n :=
  let h : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) := Homeomorph.addRight (-c.1)
  h.sets <| by
    ext x
    constructor <;> intro hx
    · -- The tangent translation preserves the nonnegative first coordinate.
      change 0 ≤ (h x) 0
      simpa [h, hc] using hx
    · -- The inverse translation preserves the same half-space for the same reason.
      change 0 ≤ x 0 + -c.1 0 at hx
      simpa [hc] using hx

/-- Helper for Exercise 1.42: in ambient coordinates, the boundary-parallel translation subtracts
the chosen boundary point. -/
private theorem boundaryParallelTranslationHomeomorph_apply_val
    (c : EuclideanHalfSpace n) (hc : c.1 0 = 0) (x : EuclideanHalfSpace n) :
    (boundaryParallelTranslationHomeomorph c hc x).1 = x.1 - c.1 := by
  rfl

/-- Helper for Exercise 1.42: the inverse boundary-parallel translation adds the chosen boundary
point back in ambient coordinates. -/
private theorem boundaryParallelTranslationHomeomorph_symm_apply_val
    (c : EuclideanHalfSpace n) (hc : c.1 0 = 0) (x : EuclideanHalfSpace n) :
    ((boundaryParallelTranslationHomeomorph c hc).symm x).1 = x.1 + c.1 := by
  -- Use the right-inverse identity and solve the ambient vector equation once.
  have h := congrArg Subtype.val ((boundaryParallelTranslationHomeomorph c hc).right_inv x)
  change ((boundaryParallelTranslationHomeomorph c hc)
      ((boundaryParallelTranslationHomeomorph c hc).symm x)).1 = x.1 at h
  rw [boundaryParallelTranslationHomeomorph_apply_val] at h
  simpa [sub_eq_add_neg, add_comm] using (sub_eq_iff_eq_add.mp h)

/-- Helper for Exercise 1.42: boundary-parallel translations belong to the smooth half-space
groupoid. -/
private theorem boundaryParallelTranslation_mem_contDiffGroupoid
    (c : EuclideanHalfSpace n) (hc : c.1 0 = 0) :
    (boundaryParallelTranslationHomeomorph c hc).toOpenPartialHomeomorph ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡∂ n) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  constructor
  · -- In the ambient Euclidean space, the forward map is the affine translation `x ↦ x - c`.
    have hforward :
        ContDiffOn ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin n) ↦ x - c.1)
          (univ : Set (EuclideanSpace ℝ (Fin n))) := by
      simpa [sub_eq_add_neg] using (contDiff_id.add contDiff_const).contDiffOn
    refine hforward.congr_mono ?_ ?_
    · intro x hx
      rcases mem_range.1 hx.2 with ⟨y, rfl⟩
      simpa using boundaryParallelTranslationHomeomorph_apply_val c hc y
    · exact inter_subset_left
  · -- The inverse ambient map is the opposite affine translation `x ↦ x + c`.
    have hreverse :
        ContDiffOn ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin n) ↦ x + c.1)
          (univ : Set (EuclideanSpace ℝ (Fin n))) := by
      simpa using (contDiff_id.add contDiff_const).contDiffOn
    refine hreverse.congr_mono ?_ ?_
    · intro x hx
      rcases mem_range.1 hx.2 with ⟨y, rfl⟩
      simpa using boundaryParallelTranslationHomeomorph_symm_apply_val c hc y
    · exact inter_subset_left

/-- Helper for Exercise 1.42: the boundary-parallel translation sends the boundary-centered model
ball `Metric.ball c r` to the zero-centered model ball `Metric.ball 0 r`. -/
private theorem boundaryParallelTranslation_image_ball
    (c : EuclideanHalfSpace n) (hc : c.1 0 = 0) (r : ℝ) :
    boundaryParallelTranslationHomeomorph c hc '' Metric.ball c r =
      Metric.ball (0 : EuclideanHalfSpace n) r := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    -- Translating by `-c` preserves the distance to the center.
    rw [Metric.mem_ball] at hw ⊢
    change dist ((boundaryParallelTranslationHomeomorph c hc w).1)
        (0 : EuclideanSpace ℝ (Fin n)) < r
    rw [boundaryParallelTranslationHomeomorph_apply_val]
    calc
      dist (w.1 - c.1) (0 : EuclideanSpace ℝ (Fin n)) = ‖(w.1 - c.1) - 0‖ := by
        simp [dist_eq_norm]
      _ = ‖w.1 - c.1‖ := by simp
      _ = dist w.1 c.1 := by simp [dist_eq_norm]
      _ = dist w c := by rfl
      _ < r := hw
  · intro hz
    -- Pulling a zero-centered ball point back by the inverse translation recovers the
    -- boundary-centered ball.
    refine ⟨(boundaryParallelTranslationHomeomorph c hc).symm z, ?_, by simp⟩
    rw [Metric.mem_ball] at hz ⊢
    change dist (((boundaryParallelTranslationHomeomorph c hc).symm z).1) c.1 < r
    rw [boundaryParallelTranslationHomeomorph_symm_apply_val]
    calc
      dist (z.1 + c.1) c.1 = ‖(z.1 + c.1) - c.1‖ := by simp [dist_eq_norm]
      _ = ‖z.1‖ := by congr 1; abel
      _ = dist z.1 (0 : EuclideanSpace ℝ (Fin n)) := by simp [dist_eq_norm]
      _ = dist z (0 : EuclideanHalfSpace n) := by rfl
      _ < r := hz

/-- Helper for Exercise 1.42: the inverse boundary-parallel translation sends the zero-centered
model ball back to the boundary-centered model ball. -/
private theorem boundaryParallelTranslation_symm_image_ball
    (c : EuclideanHalfSpace n) (hc : c.1 0 = 0) (r : ℝ) :
    (boundaryParallelTranslationHomeomorph c hc).symm '' Metric.ball (0 : EuclideanHalfSpace n) r =
      Metric.ball c r := by
  -- Apply the inverse homeomorphism to the already normalized image equality.
  calc
    (boundaryParallelTranslationHomeomorph c hc).symm '' Metric.ball (0 : EuclideanHalfSpace n) r =
        (boundaryParallelTranslationHomeomorph c hc).symm ''
          (boundaryParallelTranslationHomeomorph c hc '' Metric.ball c r) := by
      rw [boundaryParallelTranslation_image_ball c hc r]
    _ = (boundaryParallelTranslationHomeomorph c hc) ⁻¹'
          (boundaryParallelTranslationHomeomorph c hc '' Metric.ball c r) := by
      rw [Homeomorph.image_eq_preimage_symm]
      simp
    _ = Metric.ball c r := by
      exact (boundaryParallelTranslationHomeomorph c hc).preimage_image (Metric.ball c r)

/-- Helper for Exercise 1.42: restricting a maximal-atlas chart to a larger interior model ball
produces a regular coordinate ball on a smaller concentric interior model ball. -/
private theorem isRegularCoordinateBall_chartPreimageMetricBall
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    [T2Space M]
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ n) (⊤ : WithTop ℕ∞) M)
    {c : EuclideanHalfSpace n} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRc : R < c.1 0)
    (htarget : e.target = Metric.ball c R) :
    IsRegularCoordinateBall n (e.symm '' Metric.ball c r) := by
  let s : Set M := e.symm '' Metric.ball c r
  let t : Set M := e.symm '' Metric.closedBall c r
  have hsmall_target : Metric.ball c r ⊆ e.target := by
    -- The smaller interior ball lies inside the larger chart target.
    rw [htarget]
    exact Metric.ball_subset_ball (le_of_lt hrR)
  have hclosed_target : Metric.closedBall c r ⊆ e.target := by
    -- The corresponding closed ball is still compactly contained in the chart target.
    rw [htarget]
    exact Metric.closedBall_subset_ball hrR
  have hs_subset_t : s ⊆ t := by
    -- Replacing the open ball by the closed ball only enlarges the pullback.
    exact Set.image_mono (Metric.ball_subset_closedBall : _)
  have ht_closed : IsClosed t := by
    -- The pullback of the compact closed model ball is compact, hence closed in the manifold.
    have ht_compact : IsCompact t := by
      exact (isCompact_closedBall_euclideanHalfSpace c r).image_of_continuousOn
        (e.continuousOn_symm.mono hclosed_target)
    exact ht_compact.isClosed
  have hclosure_subset : closure s ⊆ t := by
    -- The closed pullback contains the small pullback, so it contains its closure.
    exact closure_minimal hs_subset_t ht_closed
  have ht_subset_source : t ⊆ e.source := by
    -- The closed pullback stays in the chart source because the closed ball stays in target.
    rw [show t = e.symm '' Metric.closedBall c r by rfl,
      e.symm_image_eq_source_inter_preimage hclosed_target]
    exact inter_subset_left
  have ht_subset_closure : t ⊆ closure s := by
    -- The inverse chart sends the closure of the small model ball into the closure of its
    -- pullback.
    have hcont : ContinuousOn e.symm (closure (Metric.ball c r)) := by
      rw [closure_ball_euclideanHalfSpace hr]
      exact e.continuousOn_symm.mono hclosed_target
    have himage :
        e.symm '' closure (Metric.ball c r) ⊆ closure s := by
      simpa [s] using
        (show e.symm '' closure (Metric.ball c r) ⊆ closure (e.symm '' Metric.ball c r) from
          hcont.image_closure)
    rw [closure_ball_euclideanHalfSpace hr] at himage
    simpa [t] using himage
  have hclosure_eq : closure s = t := by
    exact Subset.antisymm hclosure_subset ht_subset_closure
  refine ⟨e, he, ?_, c, R, r, hr, hrR, hRc, ?_, ?_, htarget⟩
  · -- The closure stays in the source because the closed pullback stays in the source.
    exact hclosure_subset.trans ht_subset_source
  · -- The chart sends the small pulled-back ball to the corresponding model ball.
    simpa [s] using e.image_symm_image_of_subset_target hsmall_target
  · -- After identifying the closure, the chart sends it to the closed model ball.
    calc
      e '' closure s = e '' t := by rw [hclosure_eq]
      _ = Metric.closedBall c r := by
        simpa [t] using e.image_symm_image_of_subset_target hclosed_target

/-- Helper for Exercise 1.42: after normalizing a boundary-centered model ball to the origin, the
existing zero-centered regular-half-ball criterion applies. -/
private theorem isRegularCoordinateHalfBall_boundaryCenteredChartPreimageMetricBall
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    [T2Space M]
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ n) (⊤ : WithTop ℕ∞) M)
    {c : EuclideanHalfSpace n} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hc : c.1 0 = 0)
    (htarget : e.target = Metric.ball c R) :
    IsRegularCoordinateHalfBall n (e.symm '' Metric.ball c r) := by
  let τ := boundaryParallelTranslationHomeomorph c hc
  let e' := e.transHomeomorph τ
  have hτ : τ.toOpenPartialHomeomorph ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡∂ n) := by
    -- Cache the model-space smoothness once before using it in atlas transport.
    exact boundaryParallelTranslation_mem_contDiffGroupoid c hc
  have he' : e' ∈ IsManifold.maximalAtlas (𝓡∂ n) (⊤ : WithTop ℕ∞) M := by
    -- Smooth boundary-parallel normalization preserves maximal-atlas membership.
    simpa [e', OpenPartialHomeomorph.transHomeomorph_eq_trans] using
      (trans_mem_maximalAtlas_of_mem_groupoid (M := M) (n := n) (e := e) he
        (chi := τ.toOpenPartialHomeomorph) hτ)
  have htarget' : e'.target = Metric.ball (0 : EuclideanHalfSpace n) R := by
    -- The boundary-centered outer ball translates to the zero-centered outer ball.
    calc
      e'.target = τ '' e.target := by
        simp [e', OpenPartialHomeomorph.transHomeomorph_eq_trans,
          OpenPartialHomeomorph.trans_target, Homeomorph.preimage_symm]
      _ = Metric.ball (0 : EuclideanHalfSpace n) R := by
        rw [htarget, boundaryParallelTranslation_image_ball c hc R]
  have hs_eq :
      e'.symm '' Metric.ball (0 : EuclideanHalfSpace n) r = e.symm '' Metric.ball c r := by
    -- The normalized inner ball pulls back to the original boundary-centered inner ball.
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨τ.symm y, ?_, ?_⟩
      · rw [← boundaryParallelTranslation_symm_image_ball c hc r]
        exact ⟨y, hy, rfl⟩
      · simp [e', OpenPartialHomeomorph.transHomeomorph_eq_trans]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨τ y, ?_, ?_⟩
      · rw [← boundaryParallelTranslation_image_ball c hc r]
        exact ⟨y, hy, rfl⟩
      · simp [e', OpenPartialHomeomorph.transHomeomorph_eq_trans]
  have hnormalized :
      IsRegularCoordinateHalfBall n
        (e'.symm '' Metric.ball (0 : EuclideanHalfSpace n) r) := by
    -- Once the center is moved to `0`, the zero-centered helper closes the regularity proof.
    exact isRegularCoordinateHalfBall_zeroCenteredChartPreimageMetricBall he' hr hrR htarget'
  simpa [hs_eq] using hnormalized

end PositiveDim

/-- Helper for Exercise 1.42: in positive boundary dimension, regular coordinate balls and regular
coordinate half-balls form a topological basis. -/
private theorem isTopologicalBasis_regularCoordinateBallHalfBall_succ
    {m : ℕ} [SmoothManifoldWithBoundary (m + 1) M] :
    TopologicalSpace.IsTopologicalBasis
      { s : Set M |
          IsRegularCoordinateBall (m + 1) s ∨
            IsRegularCoordinateHalfBall (m + 1) s } := by
  let B : Set (Set M) := { s : Set M |
    IsRegularCoordinateBall (m + 1) s ∨ IsRegularCoordinateHalfBall (m + 1) s }
  -- The local chart construction refines every open neighborhood by a regular ball or half-ball.
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro s hs
    rcases hs with hs | hs
    · simpa using hs.isOpen
    · simpa using hs.isOpen
  · let _ : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
    intro x u hx hu
    let e := chartAt (EuclideanHalfSpace (m + 1)) x
    let y : EuclideanHalfSpace (m + 1) := e x
    let w : Set (EuclideanHalfSpace (m + 1)) := e '' (e.source ∩ u)
    have he : e ∈ IsManifold.maximalAtlas (𝓡∂ (m + 1)) (⊤ : WithTop ℕ∞) M := by
      -- The preferred chart already belongs to the maximal smooth atlas.
      exact IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ (m + 1))
        (n := (⊤ : WithTop ℕ∞)) x
    have hxsource : x ∈ e.source := mem_chart_source _ x
    have hyw : y ∈ w := by
      -- The chart image of `x` lies in the chart image of the chosen neighborhood slice.
      exact ⟨x, ⟨hxsource, hx⟩, rfl⟩
    have hw_open : IsOpen w := by
      -- Chart images of open source-neighborhood intersections are open in the model.
      simpa [w] using e.isOpen_image_source_inter hu
    obtain ⟨R, hRpos, hclosed⟩ :
        ∃ R : ℝ, 0 < R ∧ Metric.closedBall y R ⊆ w := by
      -- Choose a closed model ball around the charted point inside the chart image of `u`.
      exact Metric.nhds_basis_closedBall.mem_iff.1 (hw_open.mem_nhds hyw)
    have hw_target : w ⊆ e.target := by
      -- Any chart image of a subset of the source stays in the chart target.
      simpa [w] using
        (Set.image_mono (show e.source ∩ u ⊆ e.source from inter_subset_left)).trans
          e.image_source_eq_target.subset
    have hs_subset_u {ρ : ℝ} (hρw : Metric.ball y ρ ⊆ w) :
        e.symm '' Metric.ball y ρ ⊆ u := by
      -- Pulling a model ball back through the chart keeps it inside the original neighborhood.
      have hs_subset_source_u : e.symm '' Metric.ball y ρ ⊆ e.source ∩ u := by
        refine (Set.image_mono hρw).trans ?_
        have himage : e.symm '' w = e.source ∩ u := by
          simpa [w] using e.symm_image_image_of_subset_source
            (s := e.source ∩ u) (show e.source ∩ u ⊆ e.source from inter_subset_left)
        exact himage.subset
      exact fun z hz ↦ (hs_subset_source_u hz).2
    by_cases hy_boundary : y.1 0 = 0
    · let r : ℝ := R / 2
      let eR :=
        e.trans (OpenPartialHomeomorph.ofSet (Metric.ball y R) Metric.isOpen_ball)
      have hball_target : Metric.ball y R ⊆ e.target := by
        -- The outer open ball sits in the chart target because its closed ball sits in `w`.
        exact (Metric.ball_subset_closedBall : Metric.ball y R ⊆ Metric.closedBall y R).trans
          (hclosed.trans hw_target)
      have heR : eR ∈ IsManifold.maximalAtlas (𝓡∂ (m + 1)) (⊤ : WithTop ℕ∞) M := by
        -- Restricting the target to an open model ball stays inside the maximal atlas.
        exact trans_mem_maximalAtlas_of_mem_groupoid he
          (ofSet_mem_contDiffGroupoid (I := 𝓡∂ (m + 1))
            (n := (⊤ : WithTop ℕ∞)) Metric.isOpen_ball)
      have hsourceR : eR.source = e.symm '' Metric.ball y R := by
        -- The restricted chart source is the pullback of the chosen outer ball.
        exact (e.symm_image_eq_source_inter_preimage hball_target).symm
      have htargetR : eR.target = Metric.ball y R := by
        -- The target side is exactly the chosen outer ball.
        dsimp [eR]
        exact inter_eq_left.2 hball_target
      have hsourceR_subset_u : eR.source ⊆ u := by
        -- The whole restricted chart source stays inside the original neighborhood.
        rw [hsourceR]
        exact hs_subset_u
          ((Metric.ball_subset_closedBall : Metric.ball y R ⊆ Metric.closedBall y R).trans hclosed)
      have hr : 0 < r := by
        -- Halving the positive outer radius still gives a positive inner radius.
        dsimp [r]
        linarith
      have hrR : r < R := by
        -- The inner radius is strictly smaller than the outer one.
        dsimp [r]
        linarith
      let s : Set M := eR.symm '' Metric.ball y r
      have hs_regular : IsRegularCoordinateHalfBall (m + 1) s := by
        -- The boundary-centered outer chart ball normalizes to the zero-centered regular helper.
        simpa [s, eR, y, r] using
          isRegularCoordinateHalfBall_boundaryCenteredChartPreimageMetricBall
            (M := M) (n := m + 1) (e := eR) heR hr hrR hy_boundary htargetR
      have hxsourceR : x ∈ eR.source := by
        -- The base point lies in the restricted source because its chart image is the center `y`.
        rw [hsourceR]
        refine ⟨y, Metric.mem_ball_self hRpos, ?_⟩
        simpa [y] using e.left_inv hxsource
      have hxchartR : eR x = y := by
        -- Restricting the chart target does not change the value at the chosen base point.
        simp [eR, y]
      have hxs : x ∈ s := by
        -- The base point maps to the center `y`, hence lies in every positive-radius inner ball.
        refine ⟨y, Metric.mem_ball_self hr, ?_⟩
        simpa [s, hxchartR] using eR.left_inv hxsourceR
      have hs_subset_sourceR : s ⊆ eR.source := by
        -- Pulling back a subset of the restricted target stays inside the restricted source.
        rw [show s = eR.symm '' Metric.ball y r by rfl,
          eR.symm_image_eq_source_inter_preimage
            (by rw [htargetR]; exact Metric.ball_subset_ball (le_of_lt hrR))]
        exact inter_subset_left
      have hs_subset : s ⊆ u := by
        -- The inner regular half-ball stays inside `u` because its source stays inside `u`.
        exact hs_subset_sourceR.trans hsourceR_subset_u
      exact ⟨s, Or.inr hs_regular, hxs, hs_subset⟩
    · have hy_pos : 0 < y.1 0 := by
        -- Interior points of the half-space have strictly positive boundary coordinate.
        exact lt_of_le_of_ne y.2 (Ne.symm hy_boundary)
      let outer : ℝ := min R (y.1 0 / 2)
      let inner : ℝ := outer / 2
      let eOuter :=
        e.trans (OpenPartialHomeomorph.ofSet (Metric.ball y outer) Metric.isOpen_ball)
      have houter_pos : 0 < outer := by
        -- Shrinking by the boundary coordinate keeps the outer radius positive.
        have hy_half_pos : 0 < y.1 0 / 2 := by
          linarith
        dsimp [outer]
        exact lt_min hRpos hy_half_pos
      have houter_lt_R : outer ≤ R := by
        -- The chosen outer radius is at most the original closed-ball radius.
        dsimp [outer]
        exact min_le_left _ _
      have houter_center : outer < y.1 0 := by
        -- The outer ball stays away from the boundary hyperplane.
        have hy_half_lt : y.1 0 / 2 < y.1 0 := by
          linarith
        exact lt_of_le_of_lt (min_le_right _ _) hy_half_lt
      have hinner_pos : 0 < inner := by
        -- Halving the positive outer radius still gives a positive inner radius.
        dsimp [inner]
        linarith
      have hinner_outer : inner < outer := by
        -- The inner radius is strictly smaller than the chosen outer radius.
        dsimp [inner]
        linarith
      have houter_closed : Metric.closedBall y outer ⊆ w := by
        -- The smaller closed ball still lies in the chosen open chart image.
        exact (Metric.closedBall_subset_closedBall houter_lt_R).trans hclosed
      have houter_ball : Metric.ball y outer ⊆ w := by
        -- Hence the corresponding open ball also lies in the same chart image.
        exact
          (Metric.ball_subset_closedBall : Metric.ball y outer ⊆ Metric.closedBall y outer).trans
            houter_closed
      have houter_target : Metric.ball y outer ⊆ e.target := by
        -- The restricted outer ball still lies in the chart target.
        exact houter_ball.trans hw_target
      have heOuter : eOuter ∈ IsManifold.maximalAtlas (𝓡∂ (m + 1)) (⊤ : WithTop ℕ∞) M := by
        -- Restricting to the smaller interior outer ball preserves maximal-atlas membership.
        exact trans_mem_maximalAtlas_of_mem_groupoid he
          (ofSet_mem_contDiffGroupoid (I := 𝓡∂ (m + 1))
            (n := (⊤ : WithTop ℕ∞)) Metric.isOpen_ball)
      have hsourceOuter : eOuter.source = e.symm '' Metric.ball y outer := by
        -- The restricted source is the pullback of the chosen smaller outer ball.
        exact (e.symm_image_eq_source_inter_preimage houter_target).symm
      have htargetOuter : eOuter.target = Metric.ball y outer := by
        -- The target side becomes exactly that smaller outer ball.
        dsimp [eOuter]
        exact inter_eq_left.2 houter_target
      have hsourceOuter_subset_u : eOuter.source ⊆ u := by
        -- The whole restricted chart source stays inside the original open neighborhood.
        rw [hsourceOuter]
        exact hs_subset_u houter_ball
      let s : Set M := eOuter.symm '' Metric.ball y inner
      have hs_regular : IsRegularCoordinateBall (m + 1) s := by
        -- The interior outer chart ball and the smaller concentric inner ball witness regularity.
        simpa [s, eOuter, y, outer, inner] using
          isRegularCoordinateBall_chartPreimageMetricBall
            (M := M) (n := m + 1) (e := eOuter) heOuter
            hinner_pos hinner_outer houter_center htargetOuter
      have hxsourceOuter : x ∈ eOuter.source := by
        -- The base point remains in the restricted source because `y` lies in the outer ball.
        rw [hsourceOuter]
        refine ⟨y, Metric.mem_ball_self houter_pos, ?_⟩
        simpa [y] using e.left_inv hxsource
      have hxchartOuter : eOuter x = y := by
        -- Restricting the target does not change the chart value at `x`.
        simp [eOuter, y]
      have hxs : x ∈ s := by
        -- The base point maps to the center `y`, so it lies in the inner interior ball.
        refine ⟨y, Metric.mem_ball_self hinner_pos, ?_⟩
        simpa [s, hxchartOuter] using eOuter.left_inv hxsourceOuter
      have hs_subset_sourceOuter : s ⊆ eOuter.source := by
        -- Pulling back a subset of the restricted target stays inside the restricted source.
        rw [show s = eOuter.symm '' Metric.ball y inner by rfl,
          eOuter.symm_image_eq_source_inter_preimage
            (by rw [htargetOuter]; exact Metric.ball_subset_ball (le_of_lt hinner_outer))]
        exact inter_subset_left
      have hs_subset : s ⊆ u := by
        -- The inner regular ball stays inside `u` because the outer restricted source does.
        exact hs_subset_sourceOuter.trans hsourceOuter_subset_u
      exact ⟨s, Or.inl hs_regular, hxs, hs_subset⟩

/-- Membership in the regular-ball/half-ball basis condition for a smooth manifold with boundary.
In dimension `0`, this is the existing coordinate-ball condition from Proposition 1.40; in
positive dimensions, the bundled smooth-manifold-with-boundary owner supplies the ambient
half-space chart structure needed by the regular ball and half-ball predicates. -/
def IsRegularCoordinateBallOrHalfBall (n : ℕ) {M : Type u}
    [TopologicalSpace M] [SmoothManifoldWithBoundary n M] (s : Set M) : Prop := by
  cases n with
  | zero =>
      exact IsBoundaryModelCoordinateBall 0 s
  | succ m =>
      let _ : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
      exact IsRegularCoordinateBall (m + 1) s ∨ IsRegularCoordinateHalfBall (m + 1) s

/-- A countable topological basis whose members are regular coordinate balls or regular coordinate
half-balls. In dimension `0`, this reduces to regular coordinate balls, since there are no
boundary half-balls. -/
class IsRegularCoordinateBallHalfBallBasis (n : ℕ) {M : Type u}
    [TopologicalSpace M] [SmoothManifoldWithBoundary n M] (b : Set (Set M)) : Prop where
  countable : b.Countable
  isTopologicalBasis : TopologicalSpace.IsTopologicalBasis b
  regular_or_half_ball : ∀ s ∈ b, IsRegularCoordinateBallOrHalfBall n s

-- Proof sketch: start from the countable precompact coordinate-ball/half-ball basis of
-- Proposition 1.40, then refine each basis neighborhood inside a smooth chart by choosing a
-- smaller rational ball centered either in the interior or on the boundary hyperplane.
/-- Exercise 1.42: every smooth manifold with boundary admits a countable basis consisting of
regular coordinate balls and regular coordinate half-balls. -/
theorem exists_countable_regular_coordinate_ball_half_ball_basis
    [SmoothManifoldWithBoundary n M] :
    ∃ b : Set (Set M), IsRegularCoordinateBallHalfBallBasis n b := by
  cases n with
  | zero =>
      -- In dimension `0`, Proposition 1.40 already gives a countable basis of coordinate balls,
      -- and the half-ball alternative is definitionally impossible.
      obtain ⟨b, hbCountable, hbBasis⟩ :=
        exists_countable_precompact_coordinate_ball_half_ball_basis (n := 0) (M := M)
      refine ⟨b, ?_⟩
      refine ⟨hbCountable, hbBasis.isTopologicalBasis, ?_⟩
      intro s hs
      rcases hbBasis.mem_isPrecompactBoundaryModelCoordinateBall_or_halfBall s hs with
        hsBall | hsHalf
      · -- A precompact boundary-model coordinate ball is already the required zero-dimensional
        -- regular basis element.
        simpa [IsRegularCoordinateBallOrHalfBall] using hsBall.1
      · -- In dimension `0` there are no boundary-model half-balls.
        exact False.elim hsHalf.1
  | succ m =>
      let B : Set (Set M) := { s : Set M |
        IsRegularCoordinateBall (m + 1) s ∨ IsRegularCoordinateHalfBall (m + 1) s }
      have hB : TopologicalSpace.IsTopologicalBasis B := by
        -- Positive boundary dimension is handled by the local regular-ball/half-ball refinement.
        exact isTopologicalBasis_regularCoordinateBallHalfBall_succ (M := M) (m := m)
      obtain ⟨b, hbB, hbCountable, hbBasis⟩ := hB.exists_countable
      refine ⟨b, ?_⟩
      refine ⟨hbCountable, hbBasis, ?_⟩
      intro s hs
      -- Membership in the extracted countable subbasis is exactly the desired regular disjunction.
      simpa [IsRegularCoordinateBallOrHalfBall] using hbB hs
