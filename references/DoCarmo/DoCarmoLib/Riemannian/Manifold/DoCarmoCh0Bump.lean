import Mathlib.Geometry.Manifold.BumpFunction

/-!
# do Carmo Chapter 0 bump functions

The coordinate-space part of the bump-function/locality remark is recorded as a
precise proposition.  The manifold version is obtained by transporting this
construction through a chart; later locality files use the corresponding
transported statements.
-/

open Set Metric Filter Function
open scoped ContDiff Manifold Topology

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Math.** **Euclidean bump function (do Carmo Ch. 0, Remark 5.7).**

For a point and a positive radius there is a smooth function supported in the
open ball, equal to one on the closure of a smaller neighbourhood, and taking
values in `[0,1]`.
-/
theorem exists_ch0_bump_function (p : E) {r : ℝ} (hr : 0 < r) :
    ∃ (U : Set E) (f : E → ℝ),
      IsOpen U ∧ p ∈ U ∧ closure U ⊆ ball p r ∧
        ContDiff ℝ ∞ f ∧
          (∀ q, 0 ≤ f q ∧ f q ≤ 1) ∧
            Set.EqOn f (fun _ => (1 : ℝ)) (closure U) ∧
              (∀ q, q ∉ ball p r → f q = 0) := by
  let bump : ContDiffBump p := ⟨r / 2, r, by linarith, by linarith⟩
  have hhalf : 0 < r / 2 := by linarith
  have hcl : closure (ball p (r / 2)) = closedBall p (r / 2) :=
    closure_ball p (ne_of_gt hhalf)
  refine ⟨ball p (r / 2), bump, isOpen_ball, mem_ball_self hhalf, ?_,
    bump.contDiff (n := ⊤), ?_, ?_, ?_⟩
  · rw [hcl]
    exact closedBall_subset_ball (by linarith)
  · intro q
    exact ⟨bump.nonneg' q, bump.le_one⟩
  · intro q hq
    apply bump.one_of_mem_closedBall
    rw [← hcl]
    exact hq
  · intro q hq
    apply bump.zero_of_le_dist
    have hnot : ¬dist q p < r := by
      simpa [mem_ball, dist_comm] using hq
    exact le_of_not_gt hnot

section Manifold

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

/-- **Math.** **Manifold bump function (do Carmo Ch. 0, Remark 5.7).**

Every neighbourhood `V` of `p` contains the closure of an open neighbourhood
`U` on which a globally smooth `[0,1]`-valued function is one; the function
vanishes outside `V`.
-/
theorem exists_ch0_manifold_bump_function {p : M} {V : Set M} (hV : V ∈ 𝓝 p) :
    ∃ (U : Set M) (f : M → ℝ),
      IsOpen U ∧ p ∈ U ∧ closure U ⊆ V ∧
        ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧
          (∀ q, 0 ≤ f q ∧ f q ≤ 1) ∧
            Set.EqOn f (fun _ => (1 : ℝ)) (closure U) ∧
              (∀ q, q ∉ V → f q = 0) := by
  obtain ⟨outer, _, houterV⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp hV
  obtain ⟨inner, _, hinnerOuter⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp outer.support_mem_nhds
  obtain ⟨rIn, hrIn, hinnerBall⟩ :=
    outer.exists_r_pos_lt_subset_ball isClosed_closure hinnerOuter
  let f : SmoothBumpFunction I p := outer.updateRIn rIn hrIn
  have hsupport : support f = support outer :=
    outer.support_updateRIn hrIn
  have htsupport : tsupport f = tsupport outer := by
    simp only [tsupport, hsupport]
  refine ⟨support inner, f, inner.isOpen_support, inner.c_mem_support, ?_,
    f.contMDiff, ?_, ?_, ?_⟩
  · exact hinnerOuter.trans (subset_closure.trans houterV)
  · intro q
    exact ⟨f.nonneg, f.le_one⟩
  · intro q hq
    have hqBall := hinnerBall hq
    exact f.one_of_dist_le hqBall.1 (le_of_lt hqBall.2)
  · intro q hqV
    by_contra hq
    have hqSupport : q ∈ support f := hq
    have hqOuter : q ∈ tsupport outer := by
      rw [← htsupport]
      exact subset_closure hqSupport
    exact hqV (houterV hqOuter)

end Manifold

end Riemannian
