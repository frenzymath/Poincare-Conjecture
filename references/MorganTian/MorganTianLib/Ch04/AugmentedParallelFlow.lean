import DoCarmoLib.Riemannian.Geodesic.GenericFlowJoint

/-!
# Smooth local parallel-transport operators in coordinates

The autonomous ODE on position, direction, and a linear operator produces the
parallel-transport equation along short straight coordinate paths. Joint
smoothness follows from the smooth local-flow theorem in `GenericFlowJoint`.
-/

noncomputable section

open Set Metric
open scoped ContDiff

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- **Math.** A smooth coordinate connection has a jointly smooth local family of
parallel-transport operators, normalized to the identity at time zero. -/
theorem exists_smooth_local_parallelOperator
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : ContDiff ℝ ∞ Γ) (y₀ : E) :
    ∃ (r T : ℝ) (P : E → ℝ → E →L[ℝ] E), 0 < r ∧ 0 < T ∧
      (∀ d ∈ ball (0 : E) r,
        P d 0 = ContinuousLinearMap.id ℝ E ∧
        ∀ t ∈ Ioo (-T) T,
          HasDerivAt (P d) (-((Γ (y₀ + t • d) d).comp (P d t))) t) ∧
      ContDiffOn ℝ ∞ (fun p : E × ℝ => P p.1 p.2)
        (ball (0 : E) r ×ˢ Ioo (-T) T) := by
  let F := E × E × (E →L[ℝ] E)
  let X : F → F := fun z => (z.2.1, 0, -((Γ z.1 z.2.1).comp z.2.2))
  have hX : ContDiff ℝ ∞ X := by
    exact (contDiff_snd.fst).prodMk
      (contDiff_const.prodMk
        (((hΓ.comp contDiff_fst).clm_apply contDiff_snd.fst).clm_comp
          contDiff_snd.snd).neg)
  let z₀ : F := (y₀, 0, ContinuousLinearMap.id ℝ E)
  obtain ⟨r, T, Φ, hr, hT, hΦ, hΦsmooth⟩ :=
    Riemannian.GenericFlow.exists_local_flow_joint_contDiff X hX z₀
  let init : E → F := fun d => (y₀, d, ContinuousLinearMap.id ℝ E)
  have hinit : ContDiff ℝ ∞ init :=
    contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)
  have hinit_mem : ∀ d ∈ ball (0 : E) r, init d ∈ ball z₀ r := by
    intro d hd
    change dist (y₀, d, ContinuousLinearMap.id ℝ E)
      (y₀, 0, ContinuousLinearMap.id ℝ E) < r
    simpa [mem_ball, Prod.dist_eq, max_eq_right (dist_nonneg :
      0 ≤ dist d 0), max_eq_left (dist_nonneg : 0 ≤ dist d 0)] using hd
  let P : E → ℝ → E →L[ℝ] E := fun d t => (Φ (init d) t).2.2
  have hzero : (0 : ℝ) ∈ Ioo (-T) T := ⟨neg_neg_of_pos hT, hT⟩
  have hdir : ∀ d ∈ ball (0 : E) r, ∀ t ∈ Ioo (-T) T,
      (Φ (init d) t).2.1 = d := by
    intro d hd t ht
    have hder : ∀ s ∈ Ioo (-T) T,
        HasDerivAt (fun s => (Φ (init d) s).2.1) (0 : E) s := by
      intro s hs
      exact ((hΦ (init d) (hinit_mem d hd)).2 s hs).snd.fst
    have hc := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-T) T).isPreconnected
      (fun s hs => (hder s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hder s hs).deriv) ht hzero
    simpa [((hΦ (init d) (hinit_mem d hd)).1), init] using hc
  have hpos : ∀ d ∈ ball (0 : E) r, ∀ t ∈ Ioo (-T) T,
      (Φ (init d) t).1 = y₀ + t • d := by
    intro d hd t ht
    have hder : ∀ s ∈ Ioo (-T) T,
        HasDerivAt (fun s => (Φ (init d) s).1 - s • d) (0 : E) s := by
      intro s hs
      have hp : HasDerivAt (fun s => (Φ (init d) s).1) (Φ (init d) s).2.1 s :=
        ((hΦ (init d) (hinit_mem d hd)).2 s hs).fst
      have hv := (hasDerivAt_id s).smul_const d
      convert hp.sub hv using 1 <;> first | rfl | simp [hdir d hd s hs]
    have hc := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-T) T).isPreconnected
      (fun s hs => (hder s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hder s hs).deriv) ht hzero
    have hc' : (Φ (init d) t).1 - t • d = y₀ := by
      simpa [((hΦ (init d) (hinit_mem d hd)).1), init] using hc
    exact sub_eq_iff_eq_add.mp hc'
  refine ⟨r, T, P, hr, hT, ?_, ?_⟩
  · intro d hd
    refine ⟨?_, ?_⟩
    · change (Φ (init d) 0).2.2 = _
      rw [(hΦ (init d) (hinit_mem d hd)).1]
    · intro t ht
      have hp : HasDerivAt (fun t => (Φ (init d) t).2.2)
          (-((Γ (Φ (init d) t).1 (Φ (init d) t).2.1).comp
            (Φ (init d) t).2.2)) t :=
        ((hΦ (init d) (hinit_mem d hd)).2 t ht).snd.snd
      simpa [X, P, hpos d hd t ht, hdir d hd t ht] using hp
  · have harg : ContDiff ℝ ∞ (fun p : E × ℝ => (init p.1, p.2)) :=
      (hinit.comp contDiff_fst).prodMk contDiff_snd
    exact ((hΦsmooth.comp harg.contDiffOn
      (fun p hp => ⟨hinit_mem p.1 hp.1, hp.2⟩)).snd.snd)

end MorganTianLib
