import MorganTianLib.Ch03.RicciFlow.GeneralizedEmbedding

/-!
# Morgan--Tian Ch. 3 - endpoint uniqueness and initial-time consequences

The integral-curve uniqueness theorem in `GeneralizedEmbedding` is stated on
open time intervals.  This file records the corresponding closed-interval
statement when the ambient representatives are continuous and the open slab
is dense in the prescribed closed slab.  It also records the elementary
separation between regular times and finite (or minus-infinite) initial times.
-/

open scoped ContDiff Manifold Topology
open Set

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

/- Restrict a closed-interval embedding to its open interior. -/
private def restrictIoo
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {t a b : ℝ}
    (e : S.CompatibleTimeSliceEmbedding n C t (Icc a b))
    (ht : t ∈ Ioo a b) :
    S.CompatibleTimeSliceEmbedding n C t (Ioo a b) := by
  let hsub : C ×ˢ Ioo a b ⊆ C ×ˢ Icc a b := by
    rintro ⟨x, s⟩ ⟨hx, hs⟩
    exact ⟨hx, ⟨le_of_lt hs.1, le_of_lt hs.2⟩⟩
  let incl : C ×ˢ Ioo a b → C ×ˢ Icc a b := Set.inclusion hsub
  let hincl : Topology.IsEmbedding incl := Topology.IsEmbedding.inclusion hsub
  have hemb :
      Topology.IsEmbedding (Set.restrict (C ×ˢ Ioo a b) e.toFun) := by
    have hc := e.toCompatibleEmbedding.isEmbedding.comp hincl
    convert hc using 1
    funext z
    rfl
  refine
    { toCompatibleEmbedding :=
        { toFun := e.toFun
          isEmbedding := hemb
          time_eq := ?_
          isIntegralCurveOn := ?_ }
      center_mem := ht
      source_subset := e.source_subset
      center_eq := e.center_eq }
  · intro z hz
    exact e.toCompatibleEmbedding.time_eq z (hsub hz)
  · intro x hx
    exact e.toCompatibleEmbedding.isIntegralCurveOn x hx |>.mono
      (by
        intro s hs
        exact ⟨le_of_lt hs.1, le_of_lt hs.2⟩)

/-!
Two closed-interval compatible embeddings agree once the open slab is dense
in the closed slab.  Continuity is required for the ambient representatives:
the `CompatibleEmbedding` structure only asserts an embedding of the
restricted domain, not continuity on all of `N × ℝ`.
-/
theorem GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.eqOn_Icc_of_closure
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {t a b : ℝ}
    (e₁ e₂ : S.CompatibleTimeSliceEmbedding n C t (Icc a b))
    (ht : t ∈ Ioo a b)
    (hcont₁ : Continuous e₁.toFun) (hcont₂ : Continuous e₂.toFun)
    (hclosure : closure (C ×ˢ Ioo a b) = C ×ˢ Icc a b) :
    Set.EqOn e₁.toFun e₂.toFun (C ×ˢ Icc a b) := by
  letI : T2Space N := S.t2Space
  have hopen : Set.EqOn e₁.toFun e₂.toFun (C ×ˢ Ioo a b) := by
    exact GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.eqOn_Ioo
      n (restrictIoo n e₁ ht) (restrictIoo n e₂ ht) ht
  have hclosed := hopen.closure hcont₁ hcont₂
  rw [hclosure] at hclosed
  exact hclosed

/-- A closed spatial source supplies the endpoint-density hypothesis. -/
theorem GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.eqOn_Icc_of_isClosed
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {t a b : ℝ}
    (e₁ e₂ : S.CompatibleTimeSliceEmbedding n C t (Icc a b))
    (hab : a < b) (ht : t ∈ Ioo a b)
    (hC : IsClosed C)
    (hcont₁ : Continuous e₁.toFun) (hcont₂ : Continuous e₂.toFun) :
    Set.EqOn e₁.toFun e₂.toFun (C ×ˢ Icc a b) := by
  apply GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.eqOn_Icc_of_closure
    n e₁ e₂ ht hcont₁ hcont₂
  rw [closure_prod_eq, hC.closure_eq, closure_Ioo hab.ne]

/-- A finite initial time is a lower bound for every occurring time. -/
theorem GeneralizedSpaceTime.IsInitialTime.le_time
    {S : GeneralizedSpaceTime n (N := N)} {t₀ : ℝ}
    (h : S.IsInitialTime n t₀) (x : N) : t₀ ≤ S.time x := by
  exact h.1 ⟨x, rfl⟩

/-- Every positive right neighborhood of a finite initial time contains an
occurring time. -/
theorem GeneralizedSpaceTime.IsInitialTime.exists_time_mem_Ico
    {S : GeneralizedSpaceTime n (N := N)} {t₀ : ℝ}
    (h : S.IsInitialTime n t₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : N, S.time x ∈ Ico t₀ (t₀ + ε) := by
  have hexists : ∃ x : N, S.time x < t₀ + ε := by
    by_contra! hcontra
    have hbound : t₀ + ε ∈ lowerBounds (Set.range S.time) := by
      intro y hy
      rcases hy with ⟨x, rfl⟩
      exact hcontra x
    have hle : t₀ + ε ≤ t₀ := h.2 hbound
    linarith
  obtain ⟨x, hx⟩ := hexists
  exact ⟨x, h.le_time n x, hx⟩

/-- If every occurring time is regular, then the time image is open. -/
theorem GeneralizedSpaceTime.timeRange_isOpen_of_all_regular
    {S : GeneralizedSpaceTime n (N := N)}
    (hall : ∀ t ∈ Set.range S.time, S.IsRegularTime n t) :
    IsOpen (Set.range S.time) := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  rcases hall t ht with hreg
  rcases hreg.2 with ⟨ε, hε, he⟩
  rcases he with ⟨e⟩
  rcases ht with ⟨x, hx⟩
  have hsubset : Ioo (t - ε) (t + ε) ⊆ Set.range S.time := by
    intro s hs
    refine ⟨e.toFun (x, s), ?_⟩
    exact e.toCompatibleTimeSliceEmbedding.toCompatibleEmbedding.time_toFun
      n ((S.mem_timeSlice_iff (n := n)).2 hx) hs
  have htIoo : t ∈ Ioo (t - ε) (t + ε) := by
    constructor <;> linarith
  exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds htIoo) hsubset

/-- A regular time cannot be a finite initial time: its product slab reaches
strictly earlier times along any point of the central slice. -/
theorem GeneralizedSpaceTime.IsRegularTime.not_isInitialTime
    {S : GeneralizedSpaceTime n (N := N)} {t : ℝ}
    (hreg : S.IsRegularTime n t) (hinit : S.IsInitialTime n t) : False := by
  rcases hreg.1 with ⟨x, hx⟩
  rcases hreg.2 with ⟨ε, hε, he⟩
  rcases he with ⟨e⟩
  let s : ℝ := t - ε / 2
  have hs : s ∈ Ioo (t - ε) (t + ε) := by
    constructor <;> dsimp [s] <;> linarith
  have hxSlice : x ∈ S.timeSlice n t :=
    (S.mem_timeSlice_iff (n := n)).2 hx
  have hsrange : s ∈ Set.range S.time := by
    refine ⟨e.toFun (x, s), ?_⟩
    exact e.toCompatibleTimeSliceEmbedding.toCompatibleEmbedding.time_toFun
      n (e.toCompatibleTimeSliceEmbedding.source_subset hxSlice) hs
  have hle' := hinit.1 hsrange
  dsimp [s] at hle'
  linarith

/-- A space-time containing a whole negative half-line has no finite initial
time. -/
theorem GeneralizedSpaceTime.IsInitialTime.not_hasInitialTimeNegInfinity
    {S : GeneralizedSpaceTime n (N := N)} {t₀ : ℝ}
    (hinit : S.IsInitialTime n t₀)
    (hneg : S.HasInitialTimeNegInfinity n) : False := by
  obtain ⟨A, hA⟩ := hneg
  have hboundA : t₀ ≤ A := hinit.1 (hA (mem_Iic.mpr le_rfl))
  have hmem : t₀ - 1 ∈ Set.range S.time := by
    apply hA
    change t₀ - 1 ≤ A
    linarith
  have hbound := hinit.1 hmem
  linarith

end MorganTianLib

end
