import MorganTianLib.Ch01.JacobiChartTransfer

/-!
# Poincaré Ch. 1, §1.4 — existence of Jacobi fields along a geodesic

Manifold-level **existence** of Jacobi fields with prescribed initial value
and initial covariant derivative, along a geodesic that may cross arbitrarily
many charts. This was the missing half of the manifold Jacobi theory (the
uniqueness half is `IsJacobiFieldAlongOn.eqOn_zero`): the chart-local pair
system has solutions in each chart
(`MorganTianLib.exists_isJacobiFieldOn_Icc_of_curve`), and the chart-change
covariance `IsJacobiFieldOn.transfer` now lets those solutions be glued along
a chain of charts by ODE uniqueness.

Main results:

* `IsJacobiFieldOn.congr` — the chart pair system depends only on the values
  of the fields on the interval;
* `IsJacobiFieldAlongOn.isJacobiFieldOn_of_mem_source` — **localization**: a
  manifold Jacobi field restricts to a single-chart certificate on any
  subinterval whose `γ`-image lies in one chart source (each chart-local
  witness is transferred to the target chart, then the certificates are
  glued by locality of `HasDerivWithinAt`);
* `exists_isJacobiFieldAlongOn` — **existence**: along a geodesic
  `γ : [a, b] → M` there is a Jacobi field `(J, ∇J)` with prescribed
  `J(a) = J₀`, `∇J(a) = DJ₀`. Proof by a supremum walk: the set of times up
  to which a solution exists is nonempty (single-chart solution near `a`),
  and at its supremum `c` a chart at `γ c` covers `[c − ε, c + ε]`; the old
  solution is localized into that chart, re-solved past `c` with matched
  data, and ODE uniqueness (`IsJacobiFieldOn.eqOn_of_left`) makes the two
  solutions agree on the overlap, so the glued field is again a Jacobi field.

Blueprint: `lem:exponential-differential-jacobi` (existence and uniqueness
of the Jacobi field `Y_Z` with `Y_Z(0) = 0`, `∇_X Y_Z(0) = Z`),
`lem:jacobi-field-coordinates`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Generalities -/

/-- **Math.** The chart Jacobi pair system only depends on the values of the
fields on the interval. -/
theorem IsJacobiFieldOn.congr {g : RiemannianMetric I M} {α : M}
    {u J DJ J' DJ' : ℝ → E} {a b : ℝ}
    (h : IsJacobiFieldOn (I := I) g α u J DJ a b)
    (hJ : ∀ t ∈ Icc a b, J' t = J t) (hDJ : ∀ t ∈ Icc a b, DJ' t = DJ t) :
    IsJacobiFieldOn (I := I) g α u J' DJ' a b where
  hasDerivWithinAt_fst t ht := by
    rw [hJ t ht, hDJ t ht]
    exact (h.hasDerivWithinAt_fst t ht).congr (fun y hy => hJ y hy) (hJ t ht)
  hasDerivWithinAt_snd t ht := by
    rw [hJ t ht, hDJ t ht]
    exact (h.hasDerivWithinAt_snd t ht).congr (fun y hy => hDJ y hy) (hDJ t ht)

/-- **Math.** Reading a tangent vector at `x` into the chart at `β` and
realizing the result back at `x` recovers the vector. -/
theorem tangentCoordChange_readback {β x : M}
    (hx : x ∈ (chartAt H β).source) (v : E) :
    tangentCoordChange I β x x (tangentCoordChange I x β x v) = v := by
  have h : tangentCoordChange I β x x (tangentCoordChange I x β x v)
      = tangentCoordChange I x x x v :=
    tangentCoordChange_comp (I := I)
      ⟨⟨mem_extChartAt_source (I := I) x,
        by rw [extChartAt_source]; exact hx⟩,
        mem_extChartAt_source (I := I) x⟩
  rw [h]
  exact tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) x)

/-! ### Localization of a manifold Jacobi field into one chart -/

section Localize

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** **Localization.** A manifold Jacobi field along a geodesic
restricts, on any subinterval whose `γ`-image lies in the source of one
chart `β`, to a chart-`β` certificate for the pair system on the whole
subinterval: each chart-local witness transfers to `β`
(`IsJacobiFieldOn.transfer`) on the intersected interval, and the
certificates glue by locality of `HasDerivWithinAt`. -/
theorem IsJacobiFieldAlongOn.isJacobiFieldOn_of_mem_source
    {g : RiemannianMetric I M} {γ : ℝ → M} {J DJ : ℝ → E} {a b : ℝ}
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {β : M} {c d : ℝ} (hsub : Icc c d ⊆ Icc a b)
    (hsrcβ : ∀ τ ∈ Icc c d, γ τ ∈ (chartAt H β).source) :
    IsJacobiFieldOn (I := I) g β (fun τ => extChartAt I β (γ τ))
      (chartVectorRep (I := I) γ β J) (chartVectorRep (I := I) γ β DJ)
      c d := by
  have key : ∀ t ∈ Icc c d, ∃ a' b' : ℝ, t ∈ Icc a' b' ∧
      Icc a' b' ⊆ Icc c d ∧ Icc a' b' ∈ 𝓝[Icc c d] t ∧
      IsJacobiFieldOn (I := I) g β (fun τ => extChartAt I β (γ τ))
        (chartVectorRep (I := I) γ β J) (chartVectorRep (I := I) γ β DJ)
        a' b' := by
    intro t ht
    obtain ⟨α', a₁, b₁, hab₁, ht₁, hsub₁, hnbhd₁, hsrc₁, hJF₁⟩ :=
      hJac t (hsub ht)
    refine ⟨max a₁ c, min b₁ d, ⟨max_le ht₁.1 ht.1,
      le_min ht₁.2 ht.2⟩, ?_, ?_, ?_⟩
    · exact Icc_subset_Icc (le_max_right _ _) (min_le_right _ _)
    · obtain ⟨U, hUopen, htU, hUsub⟩ := mem_nhdsWithin.1 hnbhd₁
      refine mem_nhdsWithin.2 ⟨U, hUopen, htU, fun σ hσ => ?_⟩
      have hσ₁ : σ ∈ Icc a₁ b₁ := hUsub ⟨hσ.1, hsub hσ.2⟩
      exact ⟨max_le hσ₁.1 hσ.2.1, le_min hσ₁.2 hσ.2.2⟩
    · have hgeo' : IsGeodesicOn (I := I) g γ (Icc (max a₁ c) (min b₁ d)) :=
        fun τ hτ => hgeo τ (hsub ⟨le_trans (le_max_right _ _) hτ.1,
          le_trans hτ.2 (min_le_right _ _)⟩)
      have hγc' : ∀ τ ∈ Icc (max a₁ c) (min b₁ d), ContinuousAt γ τ :=
        fun τ hτ => hγc τ (hsub ⟨le_trans (le_max_right _ _) hτ.1,
          le_trans hτ.2 (min_le_right _ _)⟩)
      have hsrcα' : ∀ τ ∈ Icc (max a₁ c) (min b₁ d),
          γ τ ∈ (chartAt H α').source :=
        fun τ hτ => hsrc₁ τ ⟨le_trans (le_max_left _ _) hτ.1,
          le_trans hτ.2 (min_le_left _ _)⟩
      have hsrcβ' : ∀ τ ∈ Icc (max a₁ c) (min b₁ d),
          γ τ ∈ (chartAt H β).source :=
        fun τ hτ => hsrcβ τ ⟨le_trans (le_max_right _ _) hτ.1,
          le_trans hτ.2 (min_le_right _ _)⟩
      exact (hJF₁.mono (le_max_left _ _) (min_le_left _ _)).transfer
        hgeo' hγc' hsrcα' hsrcβ'
  constructor
  all_goals
    intro t ht
    obtain ⟨a', b', ht', _hsub', hnbhd', hcert⟩ := key t ht
  · exact (hcert.hasDerivWithinAt_fst t ht').mono_of_mem_nhdsWithin hnbhd'
  · exact (hcert.hasDerivWithinAt_snd t ht').mono_of_mem_nhdsWithin hnbhd'

/-! ### Single-chart solve and readback -/

/-- **Math.** A single-chart Jacobi pair with prescribed chart readings at
the left endpoint, returned as an intrinsic pair of fields along `γ`: solve
the chart pair system (`exists_isJacobiFieldOn_Icc_of_curve`) and read the
solution back to the feet of `γ`. -/
theorem exists_intrinsic_chart_jacobi
    {g : RiemannianMetric I M} {γ : ℝ → M} {l r : ℝ} {β : M}
    (hlr : l ≤ r)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc l r))
    (hγc : ∀ t ∈ Icc l r, ContinuousAt γ t)
    (hsrc : ∀ τ ∈ Icc l r, γ τ ∈ (chartAt H β).source)
    (P0 Q0 : E) :
    ∃ J DJ : ℝ → E,
      IsJacobiFieldOn (I := I) g β (fun τ => extChartAt I β (γ τ))
        (chartVectorRep (I := I) γ β J) (chartVectorRep (I := I) γ β DJ)
        l r
      ∧ chartVectorRep (I := I) γ β J l = P0
      ∧ chartVectorRep (I := I) γ β DJ l = Q0
      ∧ (∀ τ ∈ Icc l r, J τ
          = tangentCoordChange I β (γ τ) (γ τ)
              (chartVectorRep (I := I) γ β J τ))
      ∧ (∀ τ ∈ Icc l r, DJ τ
          = tangentCoordChange I β (γ τ) (γ τ)
              (chartVectorRep (I := I) γ β DJ τ)) := by
  have hu_cont : ContinuousOn (fun τ => extChartAt I β (γ τ)) (Icc l r) := by
    intro τ hτ
    exact ((continuousAt_extChartAt' (I := I)
      (by rw [extChartAt_source]; exact hsrc τ hτ)).comp
        (hγc τ hτ)).continuousWithinAt
  have hu'_cont : ContinuousOn (deriv (fun τ => extChartAt I β (γ τ)))
      (Icc l r) := fun τ hτ =>
    (hgeo.continuousAt_deriv_extChartAt hτ (hγc τ hτ)
      (hsrc τ hτ)).continuousWithinAt
  have hmem : ∀ τ ∈ Icc l r, (fun τ' => extChartAt I β (γ τ')) τ
      ∈ interior (extChartAt I β).target := by
    intro τ hτ
    rw [(isOpen_extChartAt_target (I := I) β).interior_eq]
    exact (extChartAt I β).map_source
      (by rw [extChartAt_source]; exact hsrc τ hτ)
  obtain ⟨Jc, DJc, hJcl, hDJcl, hsys⟩ :=
    exists_isJacobiFieldOn_Icc_of_curve (I := I) g β
      hlr hu_cont hu'_cont hmem P0 Q0
  refine ⟨fun τ => tangentCoordChange I β (γ τ) (γ τ) (Jc τ),
    fun τ => tangentCoordChange I β (γ τ) (γ τ) (DJc τ), ?_, ?_, ?_, ?_, ?_⟩
  · -- the readbacks have chart readings `Jc`, `DJc` on `[l, r]`
    refine hsys.congr ?_ ?_
    · intro τ hτ
      show tangentCoordChange I (γ τ) β (γ τ)
        (tangentCoordChange I β (γ τ) (γ τ) (Jc τ)) = Jc τ
      exact tangentCoordChange_realize_self (I := I) (hsrc τ hτ) (Jc τ)
    · intro τ hτ
      show tangentCoordChange I (γ τ) β (γ τ)
        (tangentCoordChange I β (γ τ) (γ τ) (DJc τ)) = DJc τ
      exact tangentCoordChange_realize_self (I := I) (hsrc τ hτ) (DJc τ)
  · show tangentCoordChange I (γ l) β (γ l)
      (tangentCoordChange I β (γ l) (γ l) (Jc l)) = P0
    rw [tangentCoordChange_realize_self (I := I)
      (hsrc l (left_mem_Icc.2 hlr)) (Jc l)]
    exact hJcl
  · show tangentCoordChange I (γ l) β (γ l)
      (tangentCoordChange I β (γ l) (γ l) (DJc l)) = Q0
    rw [tangentCoordChange_realize_self (I := I)
      (hsrc l (left_mem_Icc.2 hlr)) (DJc l)]
    exact hDJcl
  · intro τ hτ
    show tangentCoordChange I β (γ τ) (γ τ) (Jc τ)
      = tangentCoordChange I β (γ τ) (γ τ)
          (tangentCoordChange I (γ τ) β (γ τ)
            (tangentCoordChange I β (γ τ) (γ τ) (Jc τ)))
    rw [tangentCoordChange_realize_self (I := I) (hsrc τ hτ) (Jc τ)]
  · intro τ hτ
    show tangentCoordChange I β (γ τ) (γ τ) (DJc τ)
      = tangentCoordChange I β (γ τ) (γ τ)
          (tangentCoordChange I (γ τ) β (γ τ)
            (tangentCoordChange I β (γ τ) (γ τ) (DJc τ)))
    rw [tangentCoordChange_realize_self (I := I) (hsrc τ hτ) (DJc τ)]

end Localize

/-! ### Existence of manifold Jacobi fields with prescribed initial data -/

section Existence

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** **Existence of Jacobi fields along a geodesic** with prescribed
initial value and initial covariant derivative (Morgan–Tian §1.4; the
existence half of the first paragraph of the proof of
`lem:exponential-differential-jacobi`). The geodesic may cross arbitrarily
many charts: the solution is continued by a supremum walk, gluing
single-chart solutions by ODE uniqueness through the chart-change
covariance of the pair system.

Blueprint: `lem:exponential-differential-jacobi`. -/
theorem exists_isJacobiFieldAlongOn
    {g : RiemannianMetric I M} {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (J₀ DJ₀ : TangentSpace I (γ a)) :
    ∃ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ a b
      ∧ J a = J₀ ∧ DJ a = DJ₀ := by
  classical
  -- a uniform chart interval around each time
  have hchart : ∀ c0 ∈ Icc a b, ∃ ε > (0 : ℝ),
      ∀ σ ∈ Icc (c0 - ε) (c0 + ε), γ σ ∈ (chartAt H (γ c0)).source := by
    intro c0 hc0
    have h1 := (hγc c0 hc0).preimage_mem_nhds
      ((chartAt H (γ c0)).open_source.mem_nhds (mem_chart_source H (γ c0)))
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.1 h1
    refine ⟨ε / 2, by linarith, fun σ hσ => hsub ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    have h2 : |σ - c0| ≤ ε / 2 :=
      abs_le.2 ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    linarith
  -- the set of right endpoints up to which a solution exists
  set S : Set ℝ := {c | c ∈ Ioc a b ∧ ∃ J DJ : ℝ → E,
    IsJacobiFieldAlongOn (I := I) g γ J DJ a c ∧ J a = J₀ ∧ DJ a = DJ₀}
    with hS
  -- initial step: a single-chart solution near `a`
  obtain ⟨ε₀, hε₀, hball₀⟩ := hchart a ⟨le_refl a, hab.le⟩
  have hstep0 : min b (a + ε₀) ∈ S := by
    set r₀ := min b (a + ε₀) with hr₀
    have har₀ : a < r₀ := lt_min hab (by linarith)
    have hr₀b : r₀ ≤ b := min_le_left _ _
    have hsub₀ : Icc a r₀ ⊆ Icc a b := Icc_subset_Icc le_rfl hr₀b
    have hsrc₀ : ∀ τ ∈ Icc a r₀, γ τ ∈ (chartAt H (γ a)).source :=
      fun τ hτ => hball₀ τ ⟨by linarith [hτ.1], le_trans hτ.2
        (le_trans (min_le_right _ _) (by linarith))⟩
    obtain ⟨J1, DJ1, hcert1, hJ1l, hDJ1l, _hJred, _hDJred⟩ :=
      exists_intrinsic_chart_jacobi (I := I) har₀.le
        (fun τ hτ => hgeo τ (hsub₀ hτ)) (fun τ hτ => hγc τ (hsub₀ hτ))
        hsrc₀ (J₀ : E) (DJ₀ : E)
    have hJ1a : J1 a = J₀ := by
      have h1 : chartVectorRep (I := I) γ (γ a) J1 a = J1 a := by
        rw [chartVectorRep_apply]
        exact tangentCoordChange_self (I := I)
          (mem_extChartAt_source (I := I) (γ a))
      rw [← h1, hJ1l]
    have hDJ1a : DJ1 a = DJ₀ := by
      have h1 : chartVectorRep (I := I) γ (γ a) DJ1 a = DJ1 a := by
        rw [chartVectorRep_apply]
        exact tangentCoordChange_self (I := I)
          (mem_extChartAt_source (I := I) (γ a))
      rw [← h1, hDJ1l]
    refine ⟨⟨har₀, hr₀b⟩, J1, DJ1, ?_, hJ1a, hDJ1a⟩
    intro t₀ ht₀
    exact ⟨γ a, a, r₀, har₀, ht₀, subset_rfl, self_mem_nhdsWithin,
      hsrc₀, hcert1⟩
  have hne : S.Nonempty := ⟨_, hstep0⟩
  have hbdd : BddAbove S := ⟨b, fun s hs => hs.1.2⟩
  set c := sSup S with hc
  have hac : a < c :=
    lt_of_lt_of_le (lt_min hab (by linarith)) (le_csSup hbdd hstep0)
  have hcb : c ≤ b := csSup_le hne fun s hs => hs.1.2
  -- chart at the supremum
  obtain ⟨ε, hε, hball⟩ := hchart c ⟨hac.le, hcb⟩
  -- a solved endpoint close below the supremum
  have hδ : (0 : ℝ) < min ε (c - a) := lt_min hε (by linarith)
  obtain ⟨c', hc'S, hc'lt⟩ :=
    exists_lt_of_lt_csSup hne (show c - min ε (c - a) < sSup S by
      rw [← hc]; linarith)
  have hc'le : c' ≤ c := le_csSup hbdd hc'S
  obtain ⟨hc'Ioc, J1, DJ1, hJac1, hJ1a, hDJ1a⟩ := hc'S
  -- the gluing window
  set l := max a (c - ε) with hl
  set r := min b (c + ε) with hr
  have hlc' : l < c' := max_lt hc'Ioc.1
    (by have := min_le_left ε (c - a); linarith)
  have hcr : c ≤ r := le_min hcb (by linarith)
  have hlc : l < c := lt_of_lt_of_le hlc' hc'le
  have hlr : l < r := lt_of_lt_of_le hlc hcr
  have hla : a ≤ l := le_max_left _ _
  have hrb : r ≤ b := min_le_left _ _
  have hsub_lr : Icc l r ⊆ Icc a b := Icc_subset_Icc hla hrb
  have hsrc_lr : ∀ τ ∈ Icc l r, γ τ ∈ (chartAt H (γ c)).source :=
    fun τ hτ => hball τ ⟨le_trans (by have := le_max_right a (c - ε); linarith)
      hτ.1, le_trans hτ.2 (min_le_right _ _)⟩
  have hgeo_lr : IsGeodesicOn (I := I) g γ (Icc l r) :=
    fun τ hτ => hgeo τ (hsub_lr hτ)
  have hγc_lr : ∀ τ ∈ Icc l r, ContinuousAt γ τ :=
    fun τ hτ => hγc τ (hsub_lr hτ)
  -- localize the old solution into the chart at `γ c` on `[l, c']`
  have hsub_ac' : Icc a c' ⊆ Icc a b := Icc_subset_Icc le_rfl hc'Ioc.2
  have hsub_lc' : Icc l c' ⊆ Icc l r :=
    Icc_subset_Icc le_rfl (le_trans hc'le hcr)
  have hloc := hJac1.isJacobiFieldOn_of_mem_source
    (fun τ hτ => hgeo τ (hsub_ac' hτ)) (fun τ hτ => hγc τ (hsub_ac' hτ))
    (Icc_subset_Icc hla le_rfl)
    (fun τ hτ => hsrc_lr τ (hsub_lc' hτ))
  -- solve in the chart at `γ c` on `[l, r]` with matched data at `l`
  obtain ⟨J2, DJ2, hcert2, hJ2l, hDJ2l, _hJred2, _hDJred2⟩ :=
    exists_intrinsic_chart_jacobi (I := I) hlr.le hgeo_lr hγc_lr hsrc_lr
      (chartVectorRep (I := I) γ (γ c) J1 l)
      (chartVectorRep (I := I) γ (γ c) DJ1 l)
  -- coefficient bound for uniqueness on `[l, c']`
  have hu_cont : ContinuousOn (fun τ => extChartAt I (γ c) (γ τ))
      (Icc l c') := by
    intro τ hτ
    exact ((continuousAt_extChartAt' (I := I)
      (by rw [extChartAt_source]; exact hsrc_lr τ (hsub_lc' hτ))).comp
        (hγc_lr τ (hsub_lc' hτ))).continuousWithinAt
  have hu'_cont : ContinuousOn
      (deriv (fun τ => extChartAt I (γ c) (γ τ))) (Icc l c') := fun τ hτ =>
    (hgeo_lr.continuousAt_deriv_extChartAt (hsub_lc' hτ)
      (hγc_lr τ (hsub_lc' hτ)) (hsrc_lr τ (hsub_lc' hτ))).continuousWithinAt
  have hmem : ∀ τ ∈ Icc l c', (fun τ' => extChartAt I (γ c) (γ τ')) τ
      ∈ interior (extChartAt I (γ c)).target := by
    intro τ hτ
    rw [(isOpen_extChartAt_target (I := I) (γ c)).interior_eq]
    exact (extChartAt I (γ c)).map_source
      (by rw [extChartAt_source]; exact hsrc_lr τ (hsub_lc' hτ))
  obtain ⟨K, hK⟩ := exists_nnnorm_jacobiPairCoeffCoord_le (I := I) g (γ c)
    hu_cont hu'_cont hmem
  -- ODE uniqueness: the two solutions agree on `[l, c']`
  have hEq := IsJacobiFieldOn.eqOn_of_left hK hloc
    (hcert2.mono le_rfl (le_trans hc'le hcr)) hJ2l.symm hDJ2l.symm
  have hJeq : ∀ τ ∈ Icc l c', J1 τ = J2 τ := by
    intro τ hτ
    have h1 := hEq.1 hτ
    have h2 := congrArg (tangentCoordChange I (γ c) (γ τ) (γ τ)) h1
    rwa [chartVectorRep_apply, chartVectorRep_apply,
      tangentCoordChange_readback (I := I) (hsrc_lr τ (hsub_lc' hτ)) (J1 τ),
      tangentCoordChange_readback (I := I) (hsrc_lr τ (hsub_lc' hτ)) (J2 τ)]
      at h2
  have hDJeq : ∀ τ ∈ Icc l c', DJ1 τ = DJ2 τ := by
    intro τ hτ
    have h1 := hEq.2 hτ
    have h2 := congrArg (tangentCoordChange I (γ c) (γ τ) (γ τ)) h1
    rwa [chartVectorRep_apply, chartVectorRep_apply,
      tangentCoordChange_readback (I := I) (hsrc_lr τ (hsub_lc' hτ)) (DJ1 τ),
      tangentCoordChange_readback (I := I) (hsrc_lr τ (hsub_lc' hτ)) (DJ2 τ)]
      at h2
  -- the glued field
  set Jg : ℝ → E := fun τ => if τ ≤ c' then J1 τ else J2 τ with hJg
  set DJg : ℝ → E := fun τ => if τ ≤ c' then DJ1 τ else DJ2 τ with hDJg
  have hJg_eq_J1 : ∀ τ ∈ Icc a c', Jg τ = J1 τ :=
    fun τ hτ => if_pos hτ.2
  have hDJg_eq_DJ1 : ∀ τ ∈ Icc a c', DJg τ = DJ1 τ :=
    fun τ hτ => if_pos hτ.2
  have hJg_eq_J2 : ∀ τ ∈ Icc l r, Jg τ = J2 τ := by
    intro τ hτ
    by_cases hτc : τ ≤ c'
    · show (if τ ≤ c' then J1 τ else J2 τ) = J2 τ
      rw [if_pos hτc]
      exact hJeq τ ⟨hτ.1, hτc⟩
    · show (if τ ≤ c' then J1 τ else J2 τ) = J2 τ
      rw [if_neg hτc]
  have hDJg_eq_DJ2 : ∀ τ ∈ Icc l r, DJg τ = DJ2 τ := by
    intro τ hτ
    by_cases hτc : τ ≤ c'
    · show (if τ ≤ c' then DJ1 τ else DJ2 τ) = DJ2 τ
      rw [if_pos hτc]
      exact hDJeq τ ⟨hτ.1, hτc⟩
    · show (if τ ≤ c' then DJ1 τ else DJ2 τ) = DJ2 τ
      rw [if_neg hτc]
  -- the glued field is a Jacobi field on `[a, r]`
  have hAlong : IsJacobiFieldAlongOn (I := I) g γ Jg DJg a r := by
    intro t₀ ht₀
    by_cases ht₀c : t₀ < c'
    · -- reuse the old chart-local witness below `c'`
      obtain ⟨α', a₁, b₁, hab₁, ht₁, hsub₁, hnbhd₁, hsrc₁, hJF₁⟩ :=
        hJac1 t₀ ⟨ht₀.1, ht₀c.le⟩
      refine ⟨α', a₁, b₁, hab₁, ht₁,
        hsub₁.trans (Icc_subset_Icc le_rfl (le_trans hc'le hcr)), ?_,
        hsrc₁, ?_⟩
      · obtain ⟨U, hUopen, htU, hUsub⟩ := mem_nhdsWithin.1 hnbhd₁
        refine mem_nhdsWithin.2 ⟨U ∩ Iio c', hUopen.inter isOpen_Iio,
          ⟨htU, ht₀c⟩, fun σ hσ => ?_⟩
        exact hUsub ⟨hσ.1.1, ⟨hσ.2.1, hσ.1.2.le⟩⟩
      · refine hJF₁.congr ?_ ?_
        · intro τ hτ
          rw [chartVectorRep_apply, chartVectorRep_apply,
            hJg_eq_J1 τ (hsub₁ hτ)]
        · intro τ hτ
          rw [chartVectorRep_apply, chartVectorRep_apply,
            hDJg_eq_DJ1 τ (hsub₁ hτ)]
    · -- above `c'`, use the chart at `γ c` on `[l, r]`
      rw [not_lt] at ht₀c
      refine ⟨γ c, l, r, hlr, ⟨le_trans hlc'.le ht₀c, ht₀.2⟩,
        Icc_subset_Icc hla le_rfl, ?_, hsrc_lr, ?_⟩
      · refine mem_nhdsWithin.2 ⟨Ioi l, isOpen_Ioi,
          lt_of_lt_of_le hlc' ht₀c, fun σ hσ => ?_⟩
        exact ⟨hσ.1.le, hσ.2.2⟩
      · refine hcert2.congr ?_ ?_
        · intro τ hτ
          rw [chartVectorRep_apply, chartVectorRep_apply, hJg_eq_J2 τ hτ]
        · intro τ hτ
          rw [chartVectorRep_apply, chartVectorRep_apply, hDJg_eq_DJ2 τ hτ]
  have hJga : Jg a = J₀ := by
    have h1 : Jg a = J1 a := hJg_eq_J1 a ⟨le_refl a, hc'Ioc.1.le⟩
    rw [h1, hJ1a]
  have hDJga : DJg a = DJ₀ := by
    have h1 : DJg a = DJ1 a := hDJg_eq_DJ1 a ⟨le_refl a, hc'Ioc.1.le⟩
    rw [h1, hDJ1a]
  have hrS : r ∈ S := ⟨⟨lt_of_lt_of_le hac hcr, hrb⟩, Jg, DJg, hAlong,
    hJga, hDJga⟩
  -- conclude: the supremum must be `b`, and then `r = b`
  rcases lt_or_eq_of_le hcb with hlt | heqb
  · exfalso
    have h1 : r ≤ c := le_csSup hbdd hrS
    have h2 : c < r := lt_min hlt (by linarith)
    linarith
  · have hrb' : r = b := by
      rw [hr, ← heqb]
      exact min_eq_left (by linarith)
    obtain ⟨_, J, DJ, hJac, hJa, hDJa⟩ := hrS
    exact ⟨J, DJ, hrb' ▸ hJac, hJa, hDJa⟩

end Existence

/-! ### Linearity and uniqueness with prescribed initial data -/

section Uniqueness

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** Two interval neighbourhoods of a time inside `[a, b]` contain a
common nondegenerate interval neighbourhood. -/
private theorem exists_common_refinement {a b t₀ a₁ b₁ a₂ b₂ : ℝ}
    (hab : a < b) (ht₀ : t₀ ∈ Icc a b)
    (hn₁ : Icc a₁ b₁ ∈ 𝓝[Icc a b] t₀) (hn₂ : Icc a₂ b₂ ∈ 𝓝[Icc a b] t₀) :
    ∃ a' b' : ℝ, a' < b' ∧ t₀ ∈ Icc a' b' ∧ Icc a' b' ⊆ Icc a b ∧
      Icc a' b' ∈ 𝓝[Icc a b] t₀ ∧ Icc a' b' ⊆ Icc a₁ b₁ ∧
      Icc a' b' ⊆ Icc a₂ b₂ := by
  obtain ⟨U₁, hU₁, htU₁, hs₁⟩ := mem_nhdsWithin.1 hn₁
  obtain ⟨U₂, hU₂, htU₂, hs₂⟩ := mem_nhdsWithin.1 hn₂
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hU₁.inter hU₂) t₀ ⟨htU₁, htU₂⟩
  have hmemU : ∀ σ ∈ Icc (max a (t₀ - δ/2)) (min b (t₀ + δ/2)),
      σ ∈ U₁ ∩ U₂ ∧ σ ∈ Icc a b := by
    intro σ hσ
    have h1 : t₀ - δ/2 ≤ σ := le_trans (le_max_right _ _) hσ.1
    have h2 : σ ≤ t₀ + δ/2 := le_trans hσ.2 (min_le_right _ _)
    have hmem : σ ∈ Metric.ball t₀ δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      have : |σ - t₀| ≤ δ/2 := abs_le.2 ⟨by linarith, by linarith⟩
      linarith
    exact ⟨hball hmem,
      ⟨le_trans (le_max_left _ _) hσ.1, le_trans hσ.2 (min_le_left _ _)⟩⟩
  refine ⟨max a (t₀ - δ/2), min b (t₀ + δ/2), ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact max_lt (lt_min hab (by linarith [ht₀.1]))
      (lt_min (by linarith [ht₀.2]) (by linarith))
  · exact max_le ht₀.1 (by linarith)
  · exact le_min ht₀.2 (by linarith)
  · exact Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  · refine mem_nhdsWithin.2 ⟨Ioo (t₀ - δ/2) (t₀ + δ/2), isOpen_Ioo,
      ⟨by linarith, by linarith⟩, fun σ hσ => ?_⟩
    exact ⟨max_le hσ.2.1 hσ.1.1.le, le_min hσ.2.2 hσ.1.2.le⟩
  · exact fun σ hσ => hs₁ ⟨(hmemU σ hσ).1.1, (hmemU σ hσ).2⟩
  · exact fun σ hσ => hs₂ ⟨(hmemU σ hσ).1.2, (hmemU σ hσ).2⟩

/-- **Math.** The difference of two Jacobi fields along a geodesic is a
Jacobi field: transfer the two chart-local certificates to a common chart on
a common interval (`IsJacobiFieldOn.transfer`) and subtract there. -/
theorem IsJacobiFieldAlongOn.sub
    {g : RiemannianMetric I M} {γ : ℝ → M} {J₁ DJ₁ J₂ DJ₂ : ℝ → E}
    {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (h₁ : IsJacobiFieldAlongOn (I := I) g γ J₁ DJ₁ a b)
    (h₂ : IsJacobiFieldAlongOn (I := I) g γ J₂ DJ₂ a b) :
    IsJacobiFieldAlongOn (I := I) g γ (fun τ => J₁ τ - J₂ τ)
      (fun τ => DJ₁ τ - DJ₂ τ) a b := by
  intro t₀ ht₀
  obtain ⟨α₁, a₁, b₁, hab₁, ht₁, hsub₁, hnbhd₁, hsrc₁, hJF₁⟩ := h₁ t₀ ht₀
  obtain ⟨α₂, a₂, b₂, hab₂, ht₂, hsub₂, hnbhd₂, hsrc₂, hJF₂⟩ := h₂ t₀ ht₀
  obtain ⟨a', b', hab', ht', hsubab, hnbhd', hsubI₁, hsubI₂⟩ :=
    exists_common_refinement hab ht₀ hnbhd₁ hnbhd₂
  have hgeo' : IsGeodesicOn (I := I) g γ (Icc a' b') :=
    fun τ hτ => hgeo τ (hsubab hτ)
  have hγc' : ∀ τ ∈ Icc a' b', ContinuousAt γ τ :=
    fun τ hτ => hγc τ (hsubab hτ)
  have hsrc₁' : ∀ τ ∈ Icc a' b', γ τ ∈ (chartAt H α₁).source :=
    fun τ hτ => hsrc₁ τ (hsubI₁ hτ)
  have hsrc₂' : ∀ τ ∈ Icc a' b', γ τ ∈ (chartAt H α₂).source :=
    fun τ hτ => hsrc₂ τ (hsubI₂ hτ)
  -- transfer the second certificate into the first chart
  have hJF₂' := (hJF₂.mono (hsubI₂ (left_mem_Icc.2 hab'.le)).1
    (hsubI₂ (right_mem_Icc.2 hab'.le)).2).transfer hgeo' hγc' hsrc₂' hsrc₁'
  have hJF₁' := hJF₁.mono (hsubI₁ (left_mem_Icc.2 hab'.le)).1
    (hsubI₁ (right_mem_Icc.2 hab'.le)).2
  -- chart-level subtraction, then congruence to the intrinsic difference
  have hcomb := hJF₁'.add (hJF₂'.const_smul (-1))
  refine ⟨α₁, a', b', hab', ht', hsubab, hnbhd', hsrc₁', hcomb.congr ?_ ?_⟩
  · intro τ hτ
    show chartVectorRep (I := I) γ α₁ (fun σ => J₁ σ - J₂ σ) τ
      = (chartVectorRep (I := I) γ α₁ J₁
          + (-1 : ℝ) • chartVectorRep (I := I) γ α₁ J₂) τ
    simp only [chartVectorRep_apply, Pi.add_apply, Pi.neg_apply,
      neg_one_smul]
    rw [map_sub]
    abel
  · intro τ hτ
    show chartVectorRep (I := I) γ α₁ (fun σ => DJ₁ σ - DJ₂ σ) τ
      = (chartVectorRep (I := I) γ α₁ DJ₁
          + (-1 : ℝ) • chartVectorRep (I := I) γ α₁ DJ₂) τ
    simp only [chartVectorRep_apply, Pi.add_apply, Pi.neg_apply,
      neg_one_smul]
    rw [map_sub]
    abel

/-- **Math.** **Superposition**: the sum of two Jacobi fields along `γ` is a Jacobi field.
Chart-level addition (`IsJacobiFieldOn.add`), after refining the two chart windows to a common
one and transferring the second certificate into the first chart — the proof of
`IsJacobiFieldAlongOn.sub` verbatim, with the sign changed.

Blueprint: `lem:second-order-linear-ode` (superposition). -/
theorem IsJacobiFieldAlongOn.add
    {g : RiemannianMetric I M} {γ : ℝ → M} {J₁ DJ₁ J₂ DJ₂ : ℝ → E}
    {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (h₁ : IsJacobiFieldAlongOn (I := I) g γ J₁ DJ₁ a b)
    (h₂ : IsJacobiFieldAlongOn (I := I) g γ J₂ DJ₂ a b) :
    IsJacobiFieldAlongOn (I := I) g γ (fun τ => J₁ τ + J₂ τ)
      (fun τ => DJ₁ τ + DJ₂ τ) a b := by
  intro t₀ ht₀
  obtain ⟨α₁, a₁, b₁, hab₁, ht₁, hsub₁, hnbhd₁, hsrc₁, hJF₁⟩ := h₁ t₀ ht₀
  obtain ⟨α₂, a₂, b₂, hab₂, ht₂, hsub₂, hnbhd₂, hsrc₂, hJF₂⟩ := h₂ t₀ ht₀
  obtain ⟨a', b', hab', ht', hsubab, hnbhd', hsubI₁, hsubI₂⟩ :=
    exists_common_refinement hab ht₀ hnbhd₁ hnbhd₂
  have hgeo' : IsGeodesicOn (I := I) g γ (Icc a' b') :=
    fun τ hτ => hgeo τ (hsubab hτ)
  have hγc' : ∀ τ ∈ Icc a' b', ContinuousAt γ τ :=
    fun τ hτ => hγc τ (hsubab hτ)
  have hsrc₁' : ∀ τ ∈ Icc a' b', γ τ ∈ (chartAt H α₁).source :=
    fun τ hτ => hsrc₁ τ (hsubI₁ hτ)
  have hsrc₂' : ∀ τ ∈ Icc a' b', γ τ ∈ (chartAt H α₂).source :=
    fun τ hτ => hsrc₂ τ (hsubI₂ hτ)
  have hJF₂' := (hJF₂.mono (hsubI₂ (left_mem_Icc.2 hab'.le)).1
    (hsubI₂ (right_mem_Icc.2 hab'.le)).2).transfer hgeo' hγc' hsrc₂' hsrc₁'
  have hJF₁' := hJF₁.mono (hsubI₁ (left_mem_Icc.2 hab'.le)).1
    (hsubI₁ (right_mem_Icc.2 hab'.le)).2
  refine ⟨α₁, a', b', hab', ht', hsubab, hnbhd', hsrc₁', (hJF₁'.add hJF₂').congr ?_ ?_⟩
  · intro τ _
    show chartVectorRep (I := I) γ α₁ (fun σ => J₁ σ + J₂ σ) τ
      = (chartVectorRep (I := I) γ α₁ J₁ + chartVectorRep (I := I) γ α₁ J₂) τ
    simp only [chartVectorRep_apply, Pi.add_apply, map_add]
  · intro τ _
    show chartVectorRep (I := I) γ α₁ (fun σ => DJ₁ σ + DJ₂ σ) τ
      = (chartVectorRep (I := I) γ α₁ DJ₁ + chartVectorRep (I := I) γ α₁ DJ₂) τ
    simp only [chartVectorRep_apply, Pi.add_apply, map_add]

/-- **Math.** **Superposition**: a scalar multiple of a Jacobi field is a Jacobi field. Only one
chart window is involved, so unlike `add`/`sub` no common refinement and no chart transfer are
needed.

Blueprint: `lem:second-order-linear-ode` (superposition). -/
theorem IsJacobiFieldAlongOn.smul
    {g : RiemannianMetric I M} {γ : ℝ → M} {J DJ : ℝ → E} {a b : ℝ} (r : ℝ)
    (h : IsJacobiFieldAlongOn (I := I) g γ J DJ a b) :
    IsJacobiFieldAlongOn (I := I) g γ (fun τ => r • J τ) (fun τ => r • DJ τ) a b := by
  intro t₀ ht₀
  obtain ⟨α, a', b', hab', ht', hsub', hnbhd', hsrc', hJF'⟩ := h t₀ ht₀
  refine ⟨α, a', b', hab', ht', hsub', hnbhd', hsrc', (hJF'.const_smul r).congr ?_ ?_⟩
  · intro τ _
    show chartVectorRep (I := I) γ α (fun σ => r • J σ) τ
      = (r • chartVectorRep (I := I) γ α J) τ
    simp only [chartVectorRep_apply, Pi.smul_apply, map_smul]
  · intro τ _
    show chartVectorRep (I := I) γ α (fun σ => r • DJ σ) τ
      = (r • chartVectorRep (I := I) γ α DJ) τ
    simp only [chartVectorRep_apply, Pi.smul_apply, map_smul]

/-- **Math.** **Uniqueness of Jacobi fields with prescribed initial data**
along a geodesic: two Jacobi fields with the same value and covariant
derivative at the left endpoint agree on the whole interval (subtract and
apply the Grönwall uniqueness `IsJacobiFieldAlongOn.eqOn_zero`). Together
with `exists_isJacobiFieldAlongOn` this is the existence-and-uniqueness of
the Jacobi field `Y_Z` in the first paragraph of the proof of
`lem:exponential-differential-jacobi`.

Blueprint: `lem:exponential-differential-jacobi`. -/
theorem IsJacobiFieldAlongOn.eqOn_of_initial
    {g : RiemannianMetric I M} {γ : ℝ → M} {J₁ DJ₁ J₂ DJ₂ : ℝ → E}
    {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (h₁ : IsJacobiFieldAlongOn (I := I) g γ J₁ DJ₁ a b)
    (h₂ : IsJacobiFieldAlongOn (I := I) g γ J₂ DJ₂ a b)
    (hJa : J₁ a = J₂ a) (hDJa : DJ₁ a = DJ₂ a) :
    ∀ t ∈ Icc a b, J₁ t = J₂ t ∧ DJ₁ t = DJ₂ t := by
  have hz := (h₁.sub hab hgeo hγc h₂).eqOn_zero hab.le hgeo hγc
    (sub_eq_zero.2 hJa) (sub_eq_zero.2 hDJa)
  intro t ht
  exact ⟨sub_eq_zero.1 (hz t ht).1, sub_eq_zero.1 (hz t ht).2⟩

end Uniqueness

end MorganTianLib

end
