import Mathlib.Analysis.Real.Sqrt
import Mathlib.Logic.Relation
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Path
import KleinerLott.RicciFlow.FlowData

/-!
# Point selection

This file gives an abstract point-picking argument for a score that increases
as its associated spatial scale decreases.
-/

namespace KleinerLott

/-- A point-selection step moves backward in time, stays within the current
scale, and increases the score by a factor greater than four. -/
def pointSelectionStep {P : Type*} (S : Set P) (time radius score scale : P → ℝ)
    (A : ℝ) (p q : P) : Prop :=
  q ∈ S ∧
    time q ≤ time p ∧
    radius q ≤ radius p + A * scale p ∧
    4 * score p < score q

/-- A bounded positive score has a point whose score controls every other score
up to any fixed multiplicative factor greater than one. -/
theorem exists_le_mul_of_bddAbove
    {P : Type*} {S : Set P} {Q : P → ℝ} {c : ℝ}
    (hne : S.Nonempty) (hpos : ∀ p ∈ S, 0 < Q p)
    (hc : 1 < c) (hbdd : BddAbove (Q '' S)) :
    ∃ p ∈ S, ∀ q ∈ S, Q q ≤ c * Q p := by
  have himage : (Q '' S).Nonempty := hne.image Q
  have hsup_pos : 0 < sSup (Q '' S) := by
    obtain ⟨p, hp⟩ := hne
    exact lt_of_lt_of_le (hpos p hp) (le_csSup hbdd ⟨p, hp, rfl⟩)
  have hc_pos : 0 < c := lt_trans zero_lt_one hc
  have hdiv : sSup (Q '' S) / c < sSup (Q '' S) := by
    rw [div_lt_iff₀ hc_pos]
    nlinarith
  obtain ⟨y, hy, hdiv_y⟩ := exists_lt_of_lt_csSup himage hdiv
  obtain ⟨p, hp, rfl⟩ := hy
  refine ⟨p, hp, ?_⟩
  intro q hq
  have hq_sup : Q q ≤ sSup (Q '' S) := le_csSup hbdd ⟨q, hq, rfl⟩
  have hsup_lt : sSup (Q '' S) < c * Q p := by
    rw [div_lt_iff₀ hc_pos] at hdiv_y
    simpa [mul_comm] using hdiv_y
  exact hq_sup.trans hsup_lt.le

/-- A bounded point-selection process terminates at a point controlling all
admissible points in its current scale. -/
theorem exists_point_of_bounded_point_selection
    {P : Type*} (S : Set P) (time radius score scale : P → ℝ)
    {p₀ : P} {A ε : ℝ}
    (hA : 0 < A) (hε : 0 < ε)
    (hp₀ : p₀ ∈ S) (htime_pos : ∀ p ∈ S, 0 < time p)
    (hradius₀ : radius p₀ ≤ ε) (hscore₀ : 0 < score p₀)
    (hscale₀ : scale p₀ ≤ ε)
    (hscale_nonneg : ∀ p ∈ S, 0 ≤ scale p)
    (hscale_shrink :
      ∀ p ∈ S, ∀ q ∈ S, 4 * score p < score q → 2 * scale q < scale p)
    (hscore_bounded :
      ∃ B, ∀ p ∈ S, time p ≤ time p₀ →
        radius p < (2 * A + 1) * ε → score p ≤ B) :
    ∃ p ∈ S, 0 < time p ∧ time p ≤ time p₀ ∧
      radius p < (2 * A + 1) * ε ∧
      ∀ q ∈ S, time q ≤ time p →
        radius q ≤ radius p + A * scale p → score q ≤ 4 * score p := by
  let step := pointSelectionStep S time radius score scale A
  let reachable : Set P := {p | Relation.ReflTransGen step p₀ p}
  have hinitial :
      radius p₀ + 2 * A * scale p₀ ≤ (2 * A + 1) * ε := by
    nlinarith
  have hinvariant :
      ∀ {p}, Relation.ReflTransGen step p₀ p →
        p ∈ S ∧
          time p ≤ time p₀ ∧
          radius p + 2 * A * scale p ≤ radius p₀ + 2 * A * scale p₀ ∧
          radius p < (2 * A + 1) * ε ∧
          0 < score p := by
    intro p hp
    induction hp with
    | refl =>
        refine ⟨hp₀, le_rfl, le_rfl, ?_, hscore₀⟩
        nlinarith [mul_pos hA hε]
    | tail hpb hbc ih =>
        rename_i b c
        rcases ih with ⟨hbS, hbtime, hbpotential, _, hbscore⟩
        rcases hbc with ⟨hcS, hctime, hcradius, hcscore⟩
        have hcscale := hscale_nonneg c hcS
        have hshrink := hscale_shrink b hbS c hcS hcscore
        have hpotential_step :
            radius c + 2 * A * scale c < radius b + 2 * A * scale b := by
          nlinarith
        refine ⟨hcS, hctime.trans hbtime, hpotential_step.le.trans hbpotential,
          ?_, ?_⟩
        · have hradius_le :
              radius c ≤ radius c + 2 * A * scale c := by
            nlinarith
          exact lt_of_le_of_lt hradius_le
            (lt_of_lt_of_le hpotential_step (hbpotential.trans hinitial))
        · nlinarith
  have hp₀_reachable : p₀ ∈ reachable := Relation.ReflTransGen.refl
  have hreachable_nonempty : reachable.Nonempty := ⟨p₀, hp₀_reachable⟩
  have hreachable_pos : ∀ p ∈ reachable, 0 < score p := by
    intro p hp
    exact (hinvariant hp).2.2.2.2
  have hreachable_bdd : BddAbove (score '' reachable) := by
    obtain ⟨B, hB⟩ := hscore_bounded
    refine ⟨B, ?_⟩
    rintro y ⟨p, hp, rfl⟩
    obtain ⟨hpS, hptime, _, hpradius, _⟩ := hinvariant hp
    exact hB p hpS hptime hpradius
  obtain ⟨p, hp, hcontrol⟩ :=
    exists_le_mul_of_bddAbove (c := (4 : ℝ)) hreachable_nonempty hreachable_pos
      (by norm_num) hreachable_bdd
  obtain ⟨hpS, hptime, _, hpradius, _⟩ := hinvariant hp
  refine ⟨p, hpS, htime_pos p hpS, hptime, hpradius, ?_⟩
  intro q hqS hqtime hqradius
  by_contra hqcontrol
  have hgrowth : 4 * score p < score q := lt_of_not_ge hqcontrol
  have hqstep : step p q := ⟨hqS, hqtime, hqradius, hgrowth⟩
  have hqreachable : q ∈ reachable := Relation.ReflTransGen.tail hp hqstep
  exact (not_lt_of_ge (hcontrol q hqreachable)) hgrowth

/-- A factor-four score increase halves the inverse-square-root scale. -/
lemma two_mul_inv_sqrt_lt_inv_sqrt {a b : ℝ} (ha : 0 < a) (hab : 4 * a < b) :
    2 * (Real.sqrt b)⁻¹ < (Real.sqrt a)⁻¹ := by
  have hsqrt : 2 * Real.sqrt a < Real.sqrt b := by
    have h := Real.sqrt_lt_sqrt (by positivity : 0 ≤ 4 * a) hab
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at h
    norm_num at h
    exact h
  have hsqrta : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hdiv : Real.sqrt a < Real.sqrt b / 2 := by linarith
  have hinv := one_div_lt_one_div_of_lt hsqrta hdiv
  simpa [one_div, div_eq_mul_inv] using hinv

/-- A lower bound by `epsilon⁻²` bounds the inverse-square-root scale by
`epsilon`. -/
lemma inv_sqrt_le_of_inv_sq_le {epsilon q : ℝ} (hepsilon : 0 < epsilon)
    (hq : (epsilon⁻¹) ^ 2 ≤ q) : (Real.sqrt q)⁻¹ ≤ epsilon := by
  have hinvpos : 0 < epsilon⁻¹ := inv_pos.2 hepsilon
  have hqpos : 0 < q := lt_of_lt_of_le (sq_pos_of_pos hinvpos) hq
  have hsqrt : epsilon⁻¹ ≤ Real.sqrt q :=
    (Real.le_sqrt hinvpos.le hqpos.le).2 hq
  have hinv := one_div_le_one_div_of_le hinvpos hsqrt
  simpa [one_div] using hinv

/-- The bounded point-picking core with the inverse-square-root curvature
scale used in the Ricci-flow argument. -/
theorem exists_point_of_bounded_curvature
    {P : Type*} (S : Set P) (time radius curvature : P → ℝ)
    {p₀ : P} {A ε : ℝ}
    (hA : 0 < A) (hε : 0 < ε)
    (hp₀ : p₀ ∈ S) (htime_pos : ∀ p ∈ S, 0 < time p)
    (hradius₀ : radius p₀ ≤ ε)
    (hcurvature_pos : ∀ p ∈ S, 0 < curvature p)
    (hcurvature₀ : (ε⁻¹) ^ 2 ≤ curvature p₀)
    (hcurvature_bounded :
      ∃ B, ∀ p ∈ S, time p ≤ time p₀ →
        radius p < (2 * A + 1) * ε → curvature p ≤ B) :
    ∃ p ∈ S, 0 < time p ∧ time p ≤ time p₀ ∧
      radius p < (2 * A + 1) * ε ∧
      ∀ q ∈ S, time q ≤ time p →
        radius q ≤ radius p + A * (Real.sqrt (curvature p))⁻¹ →
          curvature q ≤ 4 * curvature p := by
  apply exists_point_of_bounded_point_selection S time radius curvature
    (fun p => (Real.sqrt (curvature p))⁻¹) hA hε hp₀ htime_pos hradius₀
    (hcurvature_pos p₀ hp₀)
  · exact inv_sqrt_le_of_inv_sq_le hε hcurvature₀
  · intro p hp
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  · intro p hp q hq hgrowth
    exact two_mul_inv_sqrt_lt_inv_sqrt (hcurvature_pos p hp) hgrowth
  · exact hcurvature_bounded

/-- Compactness of the relevant spacetime tube supplies the curvature bound
needed by the point-picking argument. -/
theorem exists_point_of_compact_curvature
    {P : Type*} [TopologicalSpace P]
    (S K : Set P) (time radius curvature : P → ℝ)
    {p₀ : P} {A ε : ℝ}
    (hA : 0 < A) (hε : 0 < ε)
    (hp₀ : p₀ ∈ S) (htime_pos : ∀ p ∈ S, 0 < time p)
    (hradius₀ : radius p₀ ≤ ε)
    (hcurvature_pos : ∀ p ∈ S, 0 < curvature p)
    (hcurvature₀ : (ε⁻¹) ^ 2 ≤ curvature p₀)
    (hK : IsCompact K)
    (hcurvature_cont : ContinuousOn curvature K)
    (htube :
      ∀ p ∈ S, time p ≤ time p₀ →
        radius p < (2 * A + 1) * ε → p ∈ K) :
    ∃ p ∈ S, 0 < time p ∧ time p ≤ time p₀ ∧
      radius p < (2 * A + 1) * ε ∧
      ∀ q ∈ S, time q ≤ time p →
        radius q ≤ radius p + A * (Real.sqrt (curvature p))⁻¹ →
          curvature q ≤ 4 * curvature p := by
  apply exists_point_of_bounded_curvature S time radius curvature
    hA hε hp₀ htime_pos hradius₀ hcurvature_pos hcurvature₀
  obtain ⟨B, hB⟩ := hK.bddAbove_image hcurvature_cont
  refine ⟨B, ?_⟩
  intro p hp htime hradius
  exact hB ⟨p, htube p hp htime hradius, rfl⟩

namespace RicciFlowData

/-- The spacetime region where curvature is at least `alpha / t`. -/
def highCurvatureRegion {M : Type*} (flow : RicciFlowData M) (alpha : ℝ) :
    Set (M × ℝ) :=
  {p | 0 < p.2 ∧ alpha * p.2⁻¹ ≤ flow.curvatureNorm p.1 p.2}

/-- Continuous curvature is bounded on a moving spacetime tube contained in a
compact set. -/
theorem IsSpacetimePrecompactOn.exists_curvature_bound
    {M : Type*} [TopologicalSpace M]
    {flow : RicciFlowData M} {x₀ : M} {I : Set ℝ} {r : ℝ}
    (hprecompact : flow.IsSpacetimePrecompactOn x₀ I)
    (hcurvature : Continuous (Function.uncurry flow.curvatureNorm)) :
    ∃ B, ∀ x t, t ∈ I → flow.dist t x₀ x ≤ r →
      flow.curvatureNorm x t ≤ B := by
  obtain ⟨K, hK, htube⟩ := hprecompact r
  obtain ⟨B, hB⟩ := hK.bddAbove_image hcurvature.continuousOn
  refine ⟨B, ?_⟩
  intro x t ht hdist
  exact hB ⟨(x, t), htube x t ht hdist, rfl⟩

/-- Compact containment and continuous curvature give bounded curvature on all
moving balls. -/
theorem IsSpacetimePrecompactOn.isCurvatureBoundedOnMovingBalls
    {M : Type*} [TopologicalSpace M]
    {flow : RicciFlowData M} {x₀ : M} {I : Set ℝ}
    (hprecompact : flow.IsSpacetimePrecompactOn x₀ I)
    (hcurvature : Continuous (Function.uncurry flow.curvatureNorm)) :
    flow.IsCurvatureBoundedOnMovingBalls x₀ I := by
  intro r
  exact hprecompact.exists_curvature_bound (r := r) hcurvature

/-- Compact time and curvature continuity on the relevant time slab suffice to
bound curvature on all moving balls. -/
theorem IsSpacetimePrecompactOn.isCurvatureBoundedOnMovingBalls_of_continuousOn
    {M : Type*} [TopologicalSpace M]
    {flow : RicciFlowData M} {x₀ : M} {I : Set ℝ}
    (hprecompact : flow.IsSpacetimePrecompactOn x₀ I)
    (hI : IsCompact I)
    (hcurvature :
      ContinuousOn (Function.uncurry flow.curvatureNorm) (Set.univ ×ˢ I)) :
    flow.IsCurvatureBoundedOnMovingBalls x₀ I := by
  intro r
  obtain ⟨K, hK, htube⟩ := hprecompact r
  let K' : Set (M × ℝ) := K ∩ (Set.univ ×ˢ I)
  have hK' : IsCompact K' :=
    hK.inter_right (isClosed_univ.prod hI.isClosed)
  obtain ⟨B, hB⟩ :=
    hK'.bddAbove_image (hcurvature.mono fun _ hp => hp.2)
  refine ⟨B, ?_⟩
  intro x t ht hdist
  exact hB ⟨(x, t), ⟨htube x t ht hdist, ⟨Set.mem_univ x, ht⟩⟩, rfl⟩

/-- On a compact space, every moving spacetime tube over a compact time set is
contained in a compact set. -/
theorem isSpacetimePrecompactOn_of_compactSpace
    {M : Type*} [TopologicalSpace M] [CompactSpace M]
    (flow : RicciFlowData M) (x₀ : M) {I : Set ℝ} (hI : IsCompact I) :
    flow.IsSpacetimePrecompactOn x₀ I := by
  intro r
  refine ⟨Set.univ ×ˢ I, isCompact_univ.prod hI, ?_⟩
  intro x t ht _
  exact ⟨Set.mem_univ x, ht⟩

/-- Continuous curvature is bounded on bounded moving balls when the spatial
domain is compact and the time set is compact. -/
theorem isCurvatureBoundedOnMovingBalls_of_compactSpace
    {M : Type*} [TopologicalSpace M] [CompactSpace M]
    (flow : RicciFlowData M) (x₀ : M) {I : Set ℝ} (hI : IsCompact I)
    (hcurvature :
      ContinuousOn (Function.uncurry flow.curvatureNorm) (Set.univ ×ˢ I)) :
    flow.IsCurvatureBoundedOnMovingBalls x₀ I := by
  obtain ⟨B, hB⟩ := (isCompact_univ.prod hI).bddAbove_image hcurvature
  intro r
  refine ⟨B, ?_⟩
  intro x t ht _
  exact hB ⟨(x, t), ⟨Set.mem_univ x, ht⟩, rfl⟩

/-- The closed balls centered at `x₀` for the distance at time `t` are compact. -/
def IsProperAt {M : Type*} [TopologicalSpace M] (flow : RicciFlowData M)
    (x₀ : M) (t : ℝ) : Prop :=
  ∀ r, IsCompact {x | flow.dist t x₀ x ≤ r}

/-- At each time in `I`, every point can be joined to `x₀` by a path contained
in its closed distance sublevel. -/
def HasRadialDistancePathsOn {M : Type*} [TopologicalSpace M]
    (flow : RicciFlowData M) (x₀ : M) (I : Set ℝ) : Prop :=
  ∀ s ∈ I, ∀ x, ∃ γ : Path x₀ x,
    ∀ u, flow.dist s x₀ (γ u) ≤ flow.dist s x₀ x

/-- Near every time in `I`, each bounded nearby-time ball is contained in a
bounded ball for the reference-time distance. -/
def IsLocallyDistanceComparableOn {M : Type*} [TopologicalSpace M]
    (flow : RicciFlowData M) (x₀ : M) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, ∀ r, ∃ U ∈ nhds t, ∃ R,
    ∀ x s, s ∈ I → s ∈ U → flow.dist s x₀ x ≤ r → flow.dist t x₀ x ≤ R

/-- At each time in `I`, every point can be joined to `x₀` by a path staying in
an arbitrarily small enlargement of its closed distance sublevel.

This is the form supplied by a genuine length metric: the infimum defining the
Riemannian distance need not be attained, so only *almost* minimizing paths are
available without a Hopf--Rinow theorem. -/
def HasAlmostRadialDistancePathsOn {M : Type*} [TopologicalSpace M]
    (flow : RicciFlowData M) (x₀ : M) (I : Set ℝ) : Prop :=
  ∀ s ∈ I, ∀ x, ∀ delta > (0 : ℝ), ∃ γ : Path x₀ x,
    ∀ u, flow.dist s x₀ (γ u) ≤ flow.dist s x₀ x + delta

/-- Exactly radial paths are in particular almost radial. -/
theorem HasRadialDistancePathsOn.hasAlmostRadialDistancePathsOn
    {M : Type*} [TopologicalSpace M]
    {flow : RicciFlowData M} {x₀ : M} {I : Set ℝ}
    (hpaths : flow.HasRadialDistancePathsOn x₀ I) :
    flow.HasAlmostRadialDistancePathsOn x₀ I := by
  intro s hs x delta hdelta
  obtain ⟨γ, hγ⟩ := hpaths s hs x
  exact ⟨γ, fun u => (hγ u).trans (by linarith)⟩

/-- Proper reference-time balls, joint distance continuity, and almost radial
paths turn nearby moving balls into bounded reference-time balls. -/
theorem HasAlmostRadialDistancePathsOn.isLocallyDistanceComparableOn
    {M : Type*} [TopologicalSpace M]
    {flow : RicciFlowData M} {x₀ : M} {I : Set ℝ}
    (hpaths : flow.HasAlmostRadialDistancePathsOn x₀ I)
    (hproper : ∀ t ∈ I, flow.IsProperAt x₀ t)
    (hself : ∀ t ∈ I, flow.dist t x₀ x₀ = 0)
    (hcontinuous :
      ContinuousOn (Function.uncurry fun t x => flow.dist t x₀ x)
        (I ×ˢ Set.univ)) :
    flow.IsLocallyDistanceComparableOn x₀ I := by
  intro t ht r
  let R : ℝ := max r 0 + 2
  let sphere : Set M := {y | flow.dist t x₀ y = R}
  have hrR : r + 1 < R := by
    dsimp [R]
    linarith [le_max_left r 0]
  have hzeroR : 0 ≤ R := by
    dsimp [R]
    linarith [le_max_right r 0]
  have hdist_t : Continuous (fun y => flow.dist t x₀ y) :=
    hcontinuous.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨ht, Set.mem_univ y⟩)
  have hsphere_closed : IsClosed sphere :=
    isClosed_eq hdist_t continuous_const
  have hsphere_subset : sphere ⊆ {y | flow.dist t x₀ y ≤ R} := by
    intro y hy
    exact hy.le
  have hsphere_compact : IsCompact sphere :=
    (hproper t ht R).of_isClosed_subset hsphere_closed hsphere_subset
  have hsphere_eventually :
      ∀ᶠ s in nhds t, ∀ y ∈ sphere, s ∈ I → r + 1 < flow.dist s x₀ y := by
    apply hsphere_compact.eventually_forall_of_forall_eventually
    intro y hy
    have hwithin :
        {z : ℝ × M | r + 1 < flow.dist z.1 x₀ z.2} ∈
          nhdsWithin (t, y) (I ×ˢ Set.univ) := by
      apply hcontinuous (t, y) ⟨ht, Set.mem_univ y⟩
      apply Ioi_mem_nhds
      change r + 1 < flow.dist t x₀ y
      rw [hy]
      exact hrR
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hwithin
    obtain ⟨V, hV, hVsub⟩ := hwithin
    filter_upwards [hV] with z hz
    intro hzI
    exact hVsub ⟨hz, ⟨hzI, Set.mem_univ z.2⟩⟩
  refine ⟨{s | ∀ y ∈ sphere, s ∈ I → r + 1 < flow.dist s x₀ y},
    hsphere_eventually, R, ?_⟩
  intro x s hsI hsU hxs
  by_contra hx
  have hRx : R < flow.dist t x₀ x := lt_of_not_ge hx
  obtain ⟨γ, hγ⟩ := hpaths s hsI x 1 one_pos
  have hpath_cont :
      Continuous (fun u : unitInterval => flow.dist t x₀ (γ u)) :=
    hdist_t.comp γ.continuous
  have hRrange :
      R ∈ Set.range (fun u : unitInterval => flow.dist t x₀ (γ u)) := by
    apply (intermediate_value_univ (0 : unitInterval) (1 : unitInterval) hpath_cont)
    constructor
    · rw [γ.source, hself t ht]
      exact hzeroR
    · rw [γ.target]
      exact hRx.le
  obtain ⟨u, hu⟩ := hRrange
  have hysphere : γ u ∈ sphere := hu
  have hlower := hsU (γ u) hysphere hsI
  have hupper : flow.dist s x₀ (γ u) ≤ r + 1 := by
    have := hγ u
    linarith
  exact (not_lt_of_ge hupper) hlower

/-- Moving metric balls over a time set stay in bounded balls for a fixed
ambient metric. -/
def IsSpatiallyBoundedOn {M : Type*} [PseudoMetricSpace M]
    (flow : RicciFlowData M) (x₀ : M) (I : Set ℝ) : Prop :=
  ∀ r, ∃ R, ∀ x t, t ∈ I → flow.dist t x₀ x ≤ r → Dist.dist x₀ x ≤ R

/-- Moving metric balls stay uniformly bounded for times in a neighborhood of
each time in the given set. -/
def IsLocallySpatiallyBoundedOn {M : Type*} [PseudoMetricSpace M]
    (flow : RicciFlowData M) (x₀ : M) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, ∀ r, ∃ U ∈ nhds t, ∃ R,
    ∀ x s, s ∈ I → s ∈ U → flow.dist s x₀ x ≤ r → Dist.dist x₀ x ≤ R

/-- Local spatial boundedness over a compact time set places every moving ball
in a compact spacetime set. -/
theorem IsLocallySpatiallyBoundedOn.isSpacetimePrecompactOn
    {M : Type*} [PseudoMetricSpace M] [ProperSpace M]
    {flow : RicciFlowData M} {x₀ : M} {I : Set ℝ}
    (hspatial : flow.IsLocallySpatiallyBoundedOn x₀ I) (hI : IsCompact I) :
    flow.IsSpacetimePrecompactOn x₀ I := by
  classical
  intro r
  choose U hU R hR using fun t : I => hspatial t t.property r
  let U' : (t : ℝ) → t ∈ I → Set ℝ := fun t ht => U ⟨t, ht⟩
  have hU' : ∀ t ht, U' t ht ∈ nhds t := by
    intro t ht
    exact hU ⟨t, ht⟩
  obtain ⟨s, hs⟩ := hI.elim_nhds_subcover' U' hU'
  let K : I → Set (M × ℝ) :=
    fun t => Metric.closedBall x₀ (R t) ×ˢ I
  refine ⟨⋃ t ∈ s, K t, s.isCompact_biUnion (fun t _ => ?_), ?_⟩
  · exact (isCompact_closedBall x₀ (R t)).prod hI
  · intro x t ht hdist
    have ht_union : t ∈ ⋃ y ∈ s, U' y y.property := hs ht
    simp only [Set.mem_iUnion] at ht_union ⊢
    obtain ⟨y, hy, htU⟩ := ht_union
    refine ⟨y, hy, ?_⟩
    exact ⟨Metric.mem_closedBall'.2 (hR y x t ht htU hdist), ht⟩

/-- Slice-wise compactness and local distance comparison place moving balls in a
compact spacetime set. -/
theorem IsLocallyDistanceComparableOn.isSpacetimePrecompactOn
    {M : Type*} [TopologicalSpace M]
    {flow : RicciFlowData M} {x₀ : M} {I : Set ℝ}
    (hcompare : flow.IsLocallyDistanceComparableOn x₀ I)
    (hproper : ∀ t ∈ I, flow.IsProperAt x₀ t) (hI : IsCompact I) :
    flow.IsSpacetimePrecompactOn x₀ I := by
  classical
  intro r
  choose U hU R hbound using fun t : I => hcompare t t.property r
  let U' : (t : ℝ) → t ∈ I → Set ℝ := fun t ht => U ⟨t, ht⟩
  have hU' : ∀ t ht, U' t ht ∈ nhds t := by
    intro t ht
    exact hU ⟨t, ht⟩
  obtain ⟨s, hs⟩ := hI.elim_nhds_subcover' U' hU'
  let K : I → Set (M × ℝ) :=
    fun t => {x | flow.dist t x₀ x ≤ R t} ×ˢ I
  refine ⟨⋃ t ∈ s, K t, s.isCompact_biUnion (fun t _ ↦ ?_), ?_⟩
  · exact (hproper t t.property (R t)).prod hI
  · intro x t ht hdist
    have ht_union : t ∈ ⋃ y ∈ s, U' y y.property := hs ht
    simp only [Set.mem_iUnion] at ht_union ⊢
    obtain ⟨y, hy, htU⟩ := ht_union
    refine ⟨y, hy, ?_⟩
    refine ⟨?_, ht⟩
    exact hbound y x t ht htU hdist

/-- Uniform spatial boundedness over a compact time set places every moving
ball in a compact spacetime set. -/
theorem IsSpatiallyBoundedOn.isSpacetimePrecompactOn
    {M : Type*} [PseudoMetricSpace M] [ProperSpace M]
    {flow : RicciFlowData M} {x₀ : M} {I : Set ℝ}
    (hspatial : flow.IsSpatiallyBoundedOn x₀ I) (hI : IsCompact I) :
    flow.IsSpacetimePrecompactOn x₀ I := by
  intro r
  obtain ⟨R, hR⟩ := hspatial r
  refine ⟨Metric.closedBall x₀ R ×ˢ I, (isCompact_closedBall x₀ R).prod hI, ?_⟩
  intro x t ht hdist
  exact ⟨Metric.mem_closedBall'.2 (hR x t ht hdist), ht⟩

/-- Continuous curvature is bounded on a bounded moving spacetime tube in a
proper ambient space. -/
theorem IsSpatiallyBoundedOn.exists_curvature_bound
    {M : Type*} [PseudoMetricSpace M] [ProperSpace M]
    {flow : RicciFlowData M} {x₀ : M} {I : Set ℝ} {r : ℝ}
    (hI : IsCompact I) (hspatial : flow.IsSpatiallyBoundedOn x₀ I)
    (hcurvature : Continuous (Function.uncurry flow.curvatureNorm)) :
    ∃ B, ∀ x t, t ∈ I → flow.dist t x₀ x ≤ r →
      flow.curvatureNorm x t ≤ B := by
  exact (hspatial.isSpacetimePrecompactOn hI).exists_curvature_bound hcurvature

/-- Uniform spatial boundedness, compact time, and continuous curvature give
bounded curvature on all moving balls. -/
theorem IsSpatiallyBoundedOn.isCurvatureBoundedOnMovingBalls
    {M : Type*} [PseudoMetricSpace M] [ProperSpace M]
    {flow : RicciFlowData M} {x₀ : M} {I : Set ℝ}
    (hspatial : flow.IsSpatiallyBoundedOn x₀ I) (hI : IsCompact I)
    (hcurvature : Continuous (Function.uncurry flow.curvatureNorm)) :
    flow.IsCurvatureBoundedOnMovingBalls x₀ I :=
  (hspatial.isSpacetimePrecompactOn hI).isCurvatureBoundedOnMovingBalls hcurvature

/-- Local spatial boundedness, compact time, and continuous curvature give
bounded curvature on all moving balls. -/
theorem IsLocallySpatiallyBoundedOn.isCurvatureBoundedOnMovingBalls
    {M : Type*} [PseudoMetricSpace M] [ProperSpace M]
    {flow : RicciFlowData M} {x₀ : M} {I : Set ℝ}
    (hspatial : flow.IsLocallySpatiallyBoundedOn x₀ I) (hI : IsCompact I)
    (hcurvature : Continuous (Function.uncurry flow.curvatureNorm)) :
    flow.IsCurvatureBoundedOnMovingBalls x₀ I :=
  (hspatial.isSpacetimePrecompactOn hI).isCurvatureBoundedOnMovingBalls hcurvature

/-- Slice-wise compactness, local distance comparison, and continuous curvature
bound the curvature on every moving ball. -/
theorem IsLocallyDistanceComparableOn.isCurvatureBoundedOnMovingBalls
    {M : Type*} [TopologicalSpace M]
    {flow : RicciFlowData M} {x₀ : M} {I : Set ℝ}
    (hcompare : flow.IsLocallyDistanceComparableOn x₀ I)
    (hproper : ∀ t ∈ I, flow.IsProperAt x₀ t) (hI : IsCompact I)
    (hcurvature : Continuous (Function.uncurry flow.curvatureNorm)) :
    flow.IsCurvatureBoundedOnMovingBalls x₀ I :=
  (hcompare.isSpacetimePrecompactOn hproper hI).isCurvatureBoundedOnMovingBalls
    hcurvature

/-- Slice-wise compactness and interval-local curvature continuity bound
curvature on every moving ball. -/
theorem IsLocallyDistanceComparableOn.isCurvatureBoundedOnMovingBalls_of_continuousOn
    {M : Type*} [TopologicalSpace M]
    {flow : RicciFlowData M} {x₀ : M} {I : Set ℝ}
    (hcompare : flow.IsLocallyDistanceComparableOn x₀ I)
    (hproper : ∀ t ∈ I, flow.IsProperAt x₀ t) (hI : IsCompact I)
    (hcurvature :
      ContinuousOn (Function.uncurry flow.curvatureNorm) (Set.univ ×ˢ I)) :
    flow.IsCurvatureBoundedOnMovingBalls x₀ I :=
  (hcompare.isSpacetimePrecompactOn hproper hI)
    |>.isCurvatureBoundedOnMovingBalls_of_continuousOn hI hcurvature

end RicciFlowData

/-- The point-selection claim assuming curvature is bounded on bounded moving
balls over the relevant time interval. -/
theorem exists_point_selection_of_bounded_moving_curvature
    {M : Type*}
    (flow : RicciFlowData M) (n : ℕ) {alpha A epsilon t : ℝ} {x₀ x : M}
    (halpha : 0 < alpha) (hA : 0 < A) (hepsilon : 0 < epsilon)
    (_hAepsilon : A * epsilon < (100 * (n : ℝ))⁻¹)
    (ht : t ∈ Set.Ioc 0 (epsilon ^ 2))
    (hdist : flow.dist t x₀ x ≤ epsilon)
    (hcurvature :
      alpha * t⁻¹ + (epsilon⁻¹) ^ 2 ≤ flow.curvatureNorm x t)
    (hbounded :
      flow.IsCurvatureBoundedOnMovingBalls x₀ (Set.Icc 0 (epsilon ^ 2))) :
    ∃ xbar tbar,
      (xbar, tbar) ∈ flow.highCurvatureRegion alpha ∧
        tbar ∈ Set.Ioc 0 (epsilon ^ 2) ∧
        flow.dist tbar x₀ xbar < (2 * A + 1) * epsilon ∧
        ∀ x' t',
          (x', t') ∈ flow.highCurvatureRegion alpha →
            t' ≤ tbar →
              flow.dist t' x₀ x' ≤
                  flow.dist tbar x₀ xbar +
                    A * (Real.sqrt (flow.curvatureNorm xbar tbar))⁻¹ →
                flow.curvatureNorm x' t' ≤ 4 * flow.curvatureNorm xbar tbar := by
  let S : Set (M × ℝ) :=
    flow.highCurvatureRegion alpha ∩ {p | p.2 ∈ Set.Ioc 0 (epsilon ^ 2)}
  have hinitial_region : (x, t) ∈ flow.highCurvatureRegion alpha := by
    exact ⟨ht.1, le_trans (le_add_of_nonneg_right (sq_nonneg epsilon⁻¹)) hcurvature⟩
  have hinitial : (x, t) ∈ S := ⟨hinitial_region, ht⟩
  have hpositive : ∀ p ∈ S, 0 < flow.curvatureNorm p.1 p.2 := by
    intro p hp
    exact lt_of_lt_of_le (mul_pos halpha (inv_pos.mpr hp.1.1)) hp.1.2
  have hcurvature_initial :
      (epsilon⁻¹) ^ 2 ≤ flow.curvatureNorm x t := by
    have hbase_nonneg : 0 ≤ alpha * t⁻¹ :=
      (mul_pos halpha (inv_pos.mpr ht.1)).le
    exact le_trans (le_add_of_nonneg_left hbase_nonneg) hcurvature
  have hbounded_tube :
      ∃ B, ∀ p ∈ S, p.2 ≤ t →
        flow.dist p.2 x₀ p.1 < (2 * A + 1) * epsilon →
          flow.curvatureNorm p.1 p.2 ≤ B := by
    obtain ⟨B, hB⟩ := hbounded ((2 * A + 1) * epsilon)
    refine ⟨B, ?_⟩
    intro p hp _ hradius
    exact hB p.1 p.2 ⟨hp.2.1.le, hp.2.2⟩ hradius.le
  obtain ⟨p, hp, hptime_pos, _, hpradius, hcontrol⟩ :=
    exists_point_of_bounded_curvature S Prod.snd
      (fun p ↦ flow.dist p.2 x₀ p.1)
      (fun p ↦ flow.curvatureNorm p.1 p.2)
      hA hepsilon hinitial (fun p hp ↦ hp.2.1) hdist hpositive
      hcurvature_initial hbounded_tube
  refine ⟨p.1, p.2, hp.1, ⟨hptime_pos, hp.2.2⟩, hpradius, ?_⟩
  intro x' t' hx' ht' hdist'
  apply hcontrol (x', t')
  · exact ⟨hx', ⟨hx'.1, ht'.trans hp.2.2⟩⟩
  · exact ht'
  · exact hdist'

/-- The point-selection claim specialized to the high-curvature region of a
flow whose moving balls are uniformly bounded in a proper ambient metric. -/
theorem exists_point_selection_of_spatially_bounded
    {M : Type*} [PseudoMetricSpace M] [ProperSpace M]
    (flow : RicciFlowData M) (n : ℕ) {alpha A epsilon t : ℝ} {x₀ x : M}
    (halpha : 0 < alpha) (hA : 0 < A) (hepsilon : 0 < epsilon)
    (hAepsilon : A * epsilon < (100 * (n : ℝ))⁻¹)
    (ht : t ∈ Set.Ioc 0 (epsilon ^ 2))
    (hdist : flow.dist t x₀ x ≤ epsilon)
    (hcurvature :
      alpha * t⁻¹ + (epsilon⁻¹) ^ 2 ≤ flow.curvatureNorm x t)
    (hcurvature_cont : Continuous (Function.uncurry flow.curvatureNorm))
    (hspatial : flow.IsSpatiallyBoundedOn x₀ (Set.Icc 0 (epsilon ^ 2))) :
    ∃ xbar tbar,
      (xbar, tbar) ∈ flow.highCurvatureRegion alpha ∧
        tbar ∈ Set.Ioc 0 (epsilon ^ 2) ∧
        flow.dist tbar x₀ xbar < (2 * A + 1) * epsilon ∧
        ∀ x' t',
          (x', t') ∈ flow.highCurvatureRegion alpha →
            t' ∈ Set.Ioc 0 tbar →
              flow.dist t' x₀ x' ≤
                  flow.dist tbar x₀ xbar +
                    A * (Real.sqrt (flow.curvatureNorm xbar tbar))⁻¹ →
                flow.curvatureNorm x' t' ≤ 4 * flow.curvatureNorm xbar tbar := by
  have hbounded :
      flow.IsCurvatureBoundedOnMovingBalls x₀ (Set.Icc 0 (epsilon ^ 2)) :=
    hspatial.isCurvatureBoundedOnMovingBalls isCompact_Icc hcurvature_cont
  obtain ⟨xbar, tbar, hregion, htbar, hdistbar, hcontrol⟩ :=
    exists_point_selection_of_bounded_moving_curvature flow n halpha hA hepsilon
      hAepsilon ht hdist hcurvature hbounded
  refine ⟨xbar, tbar, hregion, htbar, hdistbar, ?_⟩
  intro x' t' hx' ht' hdist'
  exact hcontrol x' t' hx' ht'.2 hdist'

/-- The point-selection claim for a flow whose moving balls are locally
uniformly bounded in a proper ambient metric. -/
theorem exists_point_selection_of_locally_spatially_bounded
    {M : Type*} [PseudoMetricSpace M] [ProperSpace M]
    (flow : RicciFlowData M) (n : ℕ) {alpha A epsilon t : ℝ} {x₀ x : M}
    (halpha : 0 < alpha) (hA : 0 < A) (hepsilon : 0 < epsilon)
    (hAepsilon : A * epsilon < (100 * (n : ℝ))⁻¹)
    (ht : t ∈ Set.Ioc 0 (epsilon ^ 2))
    (hdist : flow.dist t x₀ x ≤ epsilon)
    (hcurvature :
      alpha * t⁻¹ + (epsilon⁻¹) ^ 2 ≤ flow.curvatureNorm x t)
    (hcurvature_cont : Continuous (Function.uncurry flow.curvatureNorm))
    (hspatial : flow.IsLocallySpatiallyBoundedOn x₀ (Set.Icc 0 (epsilon ^ 2))) :
    ∃ xbar tbar,
      (xbar, tbar) ∈ flow.highCurvatureRegion alpha ∧
        tbar ∈ Set.Ioc 0 (epsilon ^ 2) ∧
        flow.dist tbar x₀ xbar < (2 * A + 1) * epsilon ∧
        ∀ x' t',
          (x', t') ∈ flow.highCurvatureRegion alpha →
            t' ∈ Set.Ioc 0 tbar →
              flow.dist t' x₀ x' ≤
                  flow.dist tbar x₀ xbar +
                    A * (Real.sqrt (flow.curvatureNorm xbar tbar))⁻¹ →
                flow.curvatureNorm x' t' ≤ 4 * flow.curvatureNorm xbar tbar := by
  have hbounded :
      flow.IsCurvatureBoundedOnMovingBalls x₀ (Set.Icc 0 (epsilon ^ 2)) :=
    hspatial.isCurvatureBoundedOnMovingBalls isCompact_Icc hcurvature_cont
  obtain ⟨xbar, tbar, hregion, htbar, hdistbar, hcontrol⟩ :=
    exists_point_selection_of_bounded_moving_curvature flow n halpha hA hepsilon
      hAepsilon ht hdist hcurvature hbounded
  refine ⟨xbar, tbar, hregion, htbar, hdistbar, ?_⟩
  intro x' t' hx' ht' hdist'
  exact hcontrol x' t' hx' ht'.2 hdist'

/-- The point-selection claim from slice-wise compactness and local distance
comparison, without choosing a fixed ambient metric. -/
theorem exists_point_selection_of_locally_distance_comparable
    {M : Type*} [TopologicalSpace M]
    (flow : RicciFlowData M) (n : ℕ) {alpha A epsilon t : ℝ} {x₀ x : M}
    (halpha : 0 < alpha) (hA : 0 < A) (hepsilon : 0 < epsilon)
    (hAepsilon : A * epsilon < (100 * (n : ℝ))⁻¹)
    (ht : t ∈ Set.Ioc 0 (epsilon ^ 2))
    (hdist : flow.dist t x₀ x ≤ epsilon)
    (hcurvature :
      alpha * t⁻¹ + (epsilon⁻¹) ^ 2 ≤ flow.curvatureNorm x t)
    (hcurvature_cont : Continuous (Function.uncurry flow.curvatureNorm))
    (hcompare : flow.IsLocallyDistanceComparableOn x₀ (Set.Icc 0 (epsilon ^ 2)))
    (hproper : ∀ s ∈ Set.Icc 0 (epsilon ^ 2), flow.IsProperAt x₀ s) :
    ∃ xbar tbar,
      (xbar, tbar) ∈ flow.highCurvatureRegion alpha ∧
        tbar ∈ Set.Ioc 0 (epsilon ^ 2) ∧
        flow.dist tbar x₀ xbar < (2 * A + 1) * epsilon ∧
        ∀ x' t',
          (x', t') ∈ flow.highCurvatureRegion alpha →
            t' ∈ Set.Ioc 0 tbar →
              flow.dist t' x₀ x' ≤
                  flow.dist tbar x₀ xbar +
                    A * (Real.sqrt (flow.curvatureNorm xbar tbar))⁻¹ →
                flow.curvatureNorm x' t' ≤ 4 * flow.curvatureNorm xbar tbar := by
  have hbounded :
      flow.IsCurvatureBoundedOnMovingBalls x₀ (Set.Icc 0 (epsilon ^ 2)) :=
    hcompare.isCurvatureBoundedOnMovingBalls hproper isCompact_Icc hcurvature_cont
  obtain ⟨xbar, tbar, hregion, htbar, hdistbar, hcontrol⟩ :=
    exists_point_selection_of_bounded_moving_curvature flow n halpha hA hepsilon
      hAepsilon ht hdist hcurvature hbounded
  refine ⟨xbar, tbar, hregion, htbar, hdistbar, ?_⟩
  intro x' t' hx' ht' hdist'
  exact hcontrol x' t' hx' ht'.2 hdist'

/-- The point-selection claim for a jointly continuous proper distance family
whose closed distance sublevels admit almost radial paths.

This is the form a genuine length metric supplies: the length infimum need not
be attained, so paths only stay in an arbitrarily small enlargement of the
sublevel. -/
theorem exists_point_selection_of_almost_radial_distance_family
    {M : Type*} [TopologicalSpace M]
    (flow : RicciFlowData M) (n : ℕ) {alpha A epsilon t : ℝ} {x₀ x : M}
    (halpha : 0 < alpha) (hA : 0 < A) (hepsilon : 0 < epsilon)
    (hAepsilon : A * epsilon < (100 * (n : ℝ))⁻¹)
    (ht : t ∈ Set.Ioc 0 (epsilon ^ 2))
    (hdist : flow.dist t x₀ x ≤ epsilon)
    (hcurvature :
      alpha * t⁻¹ + (epsilon⁻¹) ^ 2 ≤ flow.curvatureNorm x t)
    (hcurvature_cont :
      ContinuousOn (Function.uncurry flow.curvatureNorm)
        (Set.univ ×ˢ Set.Icc 0 (epsilon ^ 2)))
    (hproper :
      ∀ s ∈ Set.Icc 0 (epsilon ^ 2), flow.IsProperAt x₀ s)
    (hdist_self :
      ∀ s ∈ Set.Icc 0 (epsilon ^ 2), flow.dist s x₀ x₀ = 0)
    (hdist_cont :
      ContinuousOn (Function.uncurry fun s y => flow.dist s x₀ y)
        (Set.Icc 0 (epsilon ^ 2) ×ˢ Set.univ))
    (hpaths :
      flow.HasAlmostRadialDistancePathsOn x₀ (Set.Icc 0 (epsilon ^ 2))) :
    ∃ xbar tbar,
      (xbar, tbar) ∈ flow.highCurvatureRegion alpha ∧
        tbar ∈ Set.Ioc 0 (epsilon ^ 2) ∧
        flow.dist tbar x₀ xbar < (2 * A + 1) * epsilon ∧
        ∀ x' t',
          (x', t') ∈ flow.highCurvatureRegion alpha →
            t' ∈ Set.Ioc 0 tbar →
              flow.dist t' x₀ x' ≤
                  flow.dist tbar x₀ xbar +
                    A * (Real.sqrt (flow.curvatureNorm xbar tbar))⁻¹ →
                flow.curvatureNorm x' t' ≤ 4 * flow.curvatureNorm xbar tbar := by
  have hcompare :
      flow.IsLocallyDistanceComparableOn x₀ (Set.Icc 0 (epsilon ^ 2)) :=
    hpaths.isLocallyDistanceComparableOn hproper hdist_self hdist_cont
  have hbounded :
      flow.IsCurvatureBoundedOnMovingBalls x₀ (Set.Icc 0 (epsilon ^ 2)) :=
    hcompare.isCurvatureBoundedOnMovingBalls_of_continuousOn hproper
      isCompact_Icc hcurvature_cont
  obtain ⟨xbar, tbar, hregion, htbar, hdistbar, hcontrol⟩ :=
    exists_point_selection_of_bounded_moving_curvature flow n halpha hA hepsilon
      hAepsilon ht hdist hcurvature hbounded
  refine ⟨xbar, tbar, hregion, htbar, hdistbar, ?_⟩
  intro x' t' hx' ht' hdist'
  exact hcontrol x' t' hx' ht'.2 hdist'

/-- The point-selection claim for a jointly continuous proper distance family
whose closed distance sublevels admit radial paths. -/
theorem exists_point_selection_of_continuous_proper_distance_family
    {M : Type*} [TopologicalSpace M]
    (flow : RicciFlowData M) (n : ℕ) {alpha A epsilon t : ℝ} {x₀ x : M}
    (halpha : 0 < alpha) (hA : 0 < A) (hepsilon : 0 < epsilon)
    (hAepsilon : A * epsilon < (100 * (n : ℝ))⁻¹)
    (ht : t ∈ Set.Ioc 0 (epsilon ^ 2))
    (hdist : flow.dist t x₀ x ≤ epsilon)
    (hcurvature :
      alpha * t⁻¹ + (epsilon⁻¹) ^ 2 ≤ flow.curvatureNorm x t)
    (hcurvature_cont :
      ContinuousOn (Function.uncurry flow.curvatureNorm)
        (Set.univ ×ˢ Set.Icc 0 (epsilon ^ 2)))
    (hproper :
      ∀ s ∈ Set.Icc 0 (epsilon ^ 2), flow.IsProperAt x₀ s)
    (hdist_self :
      ∀ s ∈ Set.Icc 0 (epsilon ^ 2), flow.dist s x₀ x₀ = 0)
    (hdist_cont :
      ContinuousOn (Function.uncurry fun s y => flow.dist s x₀ y)
        (Set.Icc 0 (epsilon ^ 2) ×ˢ Set.univ))
    (hpaths :
      flow.HasRadialDistancePathsOn x₀ (Set.Icc 0 (epsilon ^ 2))) :
    ∃ xbar tbar,
      (xbar, tbar) ∈ flow.highCurvatureRegion alpha ∧
        tbar ∈ Set.Ioc 0 (epsilon ^ 2) ∧
        flow.dist tbar x₀ xbar < (2 * A + 1) * epsilon ∧
        ∀ x' t',
          (x', t') ∈ flow.highCurvatureRegion alpha →
            t' ∈ Set.Ioc 0 tbar →
              flow.dist t' x₀ x' ≤
                  flow.dist tbar x₀ xbar +
                    A * (Real.sqrt (flow.curvatureNorm xbar tbar))⁻¹ →
                flow.curvatureNorm x' t' ≤ 4 * flow.curvatureNorm xbar tbar :=
  exists_point_selection_of_almost_radial_distance_family flow n halpha hA
    hepsilon hAepsilon ht hdist hcurvature hcurvature_cont hproper hdist_self
    hdist_cont hpaths.hasAlmostRadialDistancePathsOn

/-- The point-selection claim for a compact flow with continuous curvature. -/
theorem exists_point_selection_of_compactSpace
    {M : Type*} [TopologicalSpace M] [CompactSpace M]
    (flow : RicciFlowData M) (n : ℕ) {alpha A epsilon t : ℝ} {x₀ x : M}
    (halpha : 0 < alpha) (hA : 0 < A) (hepsilon : 0 < epsilon)
    (hAepsilon : A * epsilon < (100 * (n : ℝ))⁻¹)
    (ht : t ∈ Set.Ioc 0 (epsilon ^ 2))
    (hdist : flow.dist t x₀ x ≤ epsilon)
    (hcurvature :
      alpha * t⁻¹ + (epsilon⁻¹) ^ 2 ≤ flow.curvatureNorm x t)
    (hcurvature_cont :
      ContinuousOn (Function.uncurry flow.curvatureNorm)
        (Set.univ ×ˢ Set.Icc 0 (epsilon ^ 2))) :
    ∃ xbar tbar,
      (xbar, tbar) ∈ flow.highCurvatureRegion alpha ∧
        tbar ∈ Set.Ioc 0 (epsilon ^ 2) ∧
        flow.dist tbar x₀ xbar < (2 * A + 1) * epsilon ∧
        ∀ x' t',
          (x', t') ∈ flow.highCurvatureRegion alpha →
            t' ∈ Set.Ioc 0 tbar →
              flow.dist t' x₀ x' ≤
                  flow.dist tbar x₀ xbar +
                    A * (Real.sqrt (flow.curvatureNorm xbar tbar))⁻¹ →
                flow.curvatureNorm x' t' ≤ 4 * flow.curvatureNorm xbar tbar := by
  have hbounded :
      flow.IsCurvatureBoundedOnMovingBalls x₀ (Set.Icc 0 (epsilon ^ 2)) :=
    flow.isCurvatureBoundedOnMovingBalls_of_compactSpace x₀ isCompact_Icc
      hcurvature_cont
  obtain ⟨xbar, tbar, hregion, htbar, hdistbar, hcontrol⟩ :=
    exists_point_selection_of_bounded_moving_curvature flow n halpha hA hepsilon
      hAepsilon ht hdist hcurvature hbounded
  refine ⟨xbar, tbar, hregion, htbar, hdistbar, ?_⟩
  intro x' t' hx' ht' hdist'
  exact hcontrol x' t' hx' ht'.2 hdist'

end KleinerLott
