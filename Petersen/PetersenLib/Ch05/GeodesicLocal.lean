import PetersenLib.Vendored.OpenGA.Geodesic.UniformExistence

/-! # Petersen Ch. 5, §5.2 — local existence and uniqueness of geodesics

Chart-local geodesics, after Petersen, *Riemannian Geometry* (3rd ed., GTM 171),
Theorems 5.2.2 and 5.2.3. A curve `γ : ℝ → M` is a *geodesic in the chart at
`α`* on a time set `J` when its foot stays in the chart source and its chart
reading `u = φ_α ∘ γ` solves the coordinate geodesic equation
`ü = -Γ_α(u̇, u̇)(u)` on `J` (`IsChartGeodesicOn`). Equivalently, the phase lift
`z = (u, u̇)` solves the first-order coordinate spray system
`z' = (z₂, -Γ_α(z₂, z₂)(z₁)) = geodesicSprayCoord g α z₁ z₂`.

* `geodesic_local_uniqueness` (Theorem 5.2.2): two chart geodesics with the
  same position and velocity at a common time agree on the intersection of
  their (open, order-connected) time sets. Proof: Grönwall/Picard–Lindelöf
  local uniqueness for the spray system, propagated over the preconnected
  overlap by a clopen argument.
* `exists_uniform_chart_geodesic_family`: the Picard–Lindelöf local-flow
  construction behind Theorem 5.2.3 — one `ε > 0`, neighbourhoods `V₁ ∋ p`,
  `V₂ ∋ v`, and chart geodesics `c q w : (-ε, ε) → U_p` for all
  `(q, w) ∈ V₁ × V₂` with `c q w 0 = q` and initial chart velocity `w`,
  together with the flow computing the chart readings — position and
  velocity — and its Lipschitz dependence on the initial condition.
* `geodesic_local_existence` (Theorem 5.2.3): the locally-uniform existence
  statement. Its final clause — joint `C^∞`-dependence of `c q w (t)` on
  `(q, w, t)` — requires smooth dependence of ODE solutions on initial
  conditions, which is not yet in mathlib; that single conjunct is a
  documented `sorry`.
* `geodesic_local_existence_lipschitz`: a fully proven (sorry-free) variant of
  Theorem 5.2.3 in which the `C^∞`-dependence clause is replaced by the
  Lipschitz-in-initial-data estimate that mathlib's Grönwall theory provides.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff NNReal

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** **Geodesic in a chart** (Petersen §5.2). A curve `γ : ℝ → M` is a
geodesic in the chart at `α : M` on the time set `J` if its foot stays in the
chart source throughout `J` and its chart reading `u = φ_α ∘ γ` solves the
coordinate geodesic equation `ü(t) = -Γ_α(u̇(t), u̇(t))(u(t))` on `J`: the
second clause says `u` is differentiable (with derivative `u̇ = deriv u`), and
the third says `u̇` is differentiable with the prescribed Christoffel value. -/
def IsChartGeodesicOn (g : RiemannianMetric I M) (α : M) (γ : ℝ → M) (J : Set ℝ) : Prop :=
  (∀ t ∈ J, γ t ∈ (chartAt H α).source) ∧
  (∀ t ∈ J, HasDerivAt (fun s => extChartAt I α (γ s))
      (deriv (fun s => extChartAt I α (γ s)) t) t) ∧
  (∀ t ∈ J, HasDerivAt (deriv (fun s => extChartAt I α (γ s)))
      (- Geodesic.chartChristoffelContraction (I := I) g α
          (deriv (fun s => extChartAt I α (γ s)) t)
          (deriv (fun s => extChartAt I α (γ s)) t)
          (extChartAt I α (γ t))) t)

/-- **Math.** **Local uniqueness of geodesics** (Petersen Theorem 5.2.2). Two
geodesics in the chart at `α`, defined on open order-connected time sets, that
have the same position and the same chart velocity at a common time `t₀` agree
on the whole intersection of their time sets.

Proof: the phase lifts `zᵢ = (uᵢ, u̇ᵢ)` of the chart readings solve the
first-order coordinate spray system `z' = F(z)`, `F(x, w) = (w, -Γ_α(w, w)(x))`,
whose right-hand side is `C^∞` — hence locally Lipschitz — on the open set
`φ_α(U_α) × E` containing the trajectories. The agreement set is nonempty
(`t₀`), relatively closed (continuity), and relatively open
(Grönwall/Picard–Lindelöf local uniqueness), so by preconnectedness of the
open order-connected overlap it is everything; applying `φ_α⁻¹` recovers the
curves themselves. -/
theorem geodesic_local_uniqueness (g : RiemannianMetric I M) (α : M) [I.Boundaryless]
    {γ₁ γ₂ : ℝ → M} {J₁ J₂ : Set ℝ} {t₀ : ℝ}
    (hJ₁ : IsOpen J₁) (hJ₁c : J₁.OrdConnected) (hJ₂ : IsOpen J₂) (hJ₂c : J₂.OrdConnected)
    (h₁ : IsChartGeodesicOn (I := I) g α γ₁ J₁) (h₂ : IsChartGeodesicOn (I := I) g α γ₂ J₂)
    (ht₀ : t₀ ∈ J₁ ∩ J₂) (hpos : γ₁ t₀ = γ₂ t₀)
    (hvel : deriv (fun s => extChartAt I α (γ₁ s)) t₀
      = deriv (fun s => extChartAt I α (γ₂ s)) t₀) :
    Set.EqOn γ₁ γ₂ (J₁ ∩ J₂) := by
  classical
  -- phase-space lifts of the chart readings
  set z₁ : ℝ → E × E := fun s =>
    (extChartAt I α (γ₁ s), deriv (fun s' => extChartAt I α (γ₁ s')) s) with hz₁def
  set z₂ : ℝ → E × E := fun s =>
    (extChartAt I α (γ₂ s), deriv (fun s' => extChartAt I α (γ₂ s')) s) with hz₂def
  -- the phase curves solve the first-order coordinate spray system
  have hz₁d : ∀ t ∈ J₁, HasDerivAt z₁
      (Geodesic.geodesicSprayCoord (I := I) g α (z₁ t).1 (z₁ t).2) t := by
    intro t ht
    have h := (h₁.2.1 t ht).prodMk (h₁.2.2 t ht)
    exact h
  have hz₂d : ∀ t ∈ J₂, HasDerivAt z₂
      (Geodesic.geodesicSprayCoord (I := I) g α (z₂ t).1 (z₂ t).2) t := by
    intro t ht
    have h := (h₂.2.1 t ht).prodMk (h₂.2.2 t ht)
    exact h
  -- the first phase curve stays in the chart-target region where the spray is smooth
  have hz₁mem : ∀ t ∈ J₁, z₁ t ∈ (extChartAt I α).target ×ˢ (univ : Set E) := by
    intro t ht
    have hsrc : γ₁ t ∈ (extChartAt I α).source := by
      rw [extChartAt_source I]
      exact h₁.1 t ht
    exact ⟨(extChartAt I α).map_source hsrc, mem_univ _⟩
  -- the overlap is open and preconnected
  have hJo : IsOpen (J₁ ∩ J₂) := hJ₁.inter hJ₂
  have hJc : IsPreconnected (J₁ ∩ J₂) := (hJ₁c.inter hJ₂c).isPreconnected
  haveI : PreconnectedSpace ↥(J₁ ∩ J₂) := isPreconnected_iff_preconnectedSpace.mp hJc
  -- the agreement set, as a subset of the overlap
  set A : Set ↥(J₁ ∩ J₂) := {t : ↥(J₁ ∩ J₂) | z₁ (t : ℝ) = z₂ (t : ℝ)} with hAdef
  have hA_nonempty : A.Nonempty := by
    refine ⟨⟨t₀, ht₀⟩, ?_⟩
    show z₁ t₀ = z₂ t₀
    show (extChartAt I α (γ₁ t₀), deriv (fun s' => extChartAt I α (γ₁ s')) t₀)
      = (extChartAt I α (γ₂ t₀), deriv (fun s' => extChartAt I α (γ₂ s')) t₀)
    rw [hpos, hvel]
  -- closed: continuity of the phase curves
  have hz₁cont : ContinuousOn z₁ (J₁ ∩ J₂) := fun t ht =>
    (hz₁d t ht.1).continuousAt.continuousWithinAt
  have hz₂cont : ContinuousOn z₂ (J₁ ∩ J₂) := fun t ht =>
    (hz₂d t ht.2).continuousAt.continuousWithinAt
  have hAclosed : IsClosed A :=
    isClosed_eq (continuousOn_iff_continuous_restrict.mp hz₁cont)
      (continuousOn_iff_continuous_restrict.mp hz₂cont)
  -- open: local Picard–Lindelöf/Grönwall uniqueness at each agreement time
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t₁ ht₁
    have hzeq : z₁ (t₁ : ℝ) = z₂ (t₁ : ℝ) := ht₁
    have hmem₁ : z₁ (t₁ : ℝ) ∈ (extChartAt I α).target ×ˢ (univ : Set E) :=
      hz₁mem _ t₁.2.1
    have hopen : IsOpen ((extChartAt I α).target ×ˢ (univ : Set E)) :=
      (isOpen_extChartAt_target α).prod isOpen_univ
    -- the spray is `C^1` at the agreement point, hence locally Lipschitz there
    have hC1 : ContDiffAt ℝ 1
        (fun ζ : E × E => Geodesic.geodesicSprayCoord (I := I) g α ζ.1 ζ.2)
        (z₁ (t₁ : ℝ)) :=
      ((Geodesic.contDiffOn_geodesicSprayCoord_prod (I := I) g α).contDiffAt
        (hopen.mem_nhds hmem₁)).of_le (by norm_num)
    obtain ⟨K, sLip, hsLip, hlip⟩ := hC1.exists_lipschitzOnWith
    -- two-sided local uniqueness for the autonomous ODE `z' = F(z)`
    have hev : z₁ =ᶠ[𝓝 (t₁ : ℝ)] z₂ := by
      refine ODE_solution_unique_of_eventually
        (v := fun _ : ℝ => fun ζ : E × E =>
          Geodesic.geodesicSprayCoord (I := I) g α ζ.1 ζ.2)
        (s := fun _ : ℝ => sLip) (K := K)
        (Eventually.of_forall fun _ => hlip) ?_ ?_ hzeq
      · filter_upwards [hJ₁.mem_nhds t₁.2.1,
          (hz₁d _ t₁.2.1).continuousAt.eventually_mem hsLip] with t ht hts
        exact ⟨hz₁d t ht, hts⟩
      · have hsLip₂ : sLip ∈ 𝓝 (z₂ (t₁ : ℝ)) := hzeq ▸ hsLip
        filter_upwards [hJ₂.mem_nhds t₁.2.2,
          (hz₂d _ t₁.2.2).continuousAt.eventually_mem hsLip₂] with t ht hts
        exact ⟨hz₂d t ht, hts⟩
    rcases Filter.eventually_iff_exists_mem.mp hev with ⟨U, hU_nhds, hU_eq⟩
    rcases _root_.mem_nhds_iff.mp hU_nhds with ⟨V, hVU, hV_open, hV_mem⟩
    refine Filter.mem_of_superset
      ((hV_open.preimage continuous_subtype_val).mem_nhds hV_mem) ?_
    intro s hs
    exact hU_eq _ (hVU hs)
  -- clopen ⟹ the phase curves agree on the whole overlap
  have hA_univ : A = univ := IsClopen.eq_univ ⟨hAclosed, hAopen⟩ hA_nonempty
  intro t ht
  have hzt : z₁ t = z₂ t := by
    have hmem : (⟨t, ht⟩ : ↥(J₁ ∩ J₂)) ∈ (univ : Set ↥(J₁ ∩ J₂)) := mem_univ _
    rw [← hA_univ] at hmem
    exact hmem
  have hu : extChartAt I α (γ₁ t) = extChartAt I α (γ₂ t) := congrArg Prod.fst hzt
  have h1s : γ₁ t ∈ (extChartAt I α).source := by
    rw [extChartAt_source I]; exact h₁.1 t ht.1
  have h2s : γ₂ t ∈ (extChartAt I α).source := by
    rw [extChartAt_source I]; exact h₂.1 t ht.2
  calc γ₁ t = (extChartAt I α).symm (extChartAt I α (γ₁ t)) :=
        ((extChartAt I α).left_inv h1s).symm
    _ = (extChartAt I α).symm (extChartAt I α (γ₂ t)) := by rw [hu]
    _ = γ₂ t := (extChartAt I α).left_inv h2s

/-- **Math.** **The uniform chart-geodesic family from the local flow** (the
construction behind Petersen Theorem 5.2.3). Picard–Lindelöf applied to the
coordinate spray `F(x, w) = (w, -Γ_p(w, w)(x))` at the initial condition
`(φ_p(p), v)` produces: a time `ε > 0`, neighbourhoods `V₁` of `p` and `V₂` of
`v`, a family `c : M → E → ℝ → M`, a radius `r > 0` and a local flow `Z` such
that for all `(q, w) ∈ V₁ × V₂`:

* `(φ_p(q), w)` lies in the flow ball `closedBall (φ_p(p), v) r`;
* `c q w` is a geodesic in the chart at `p` on `(-ε, ε)` with `c q w 0 = q`
  and initial chart velocity `w`;
* the chart reading of `c q w` is computed by the flow:
  `φ_p(c q w t) = (Z (φ_p(q), w) t).1` on `[-ε, ε]`;
* the flow is `L`-Lipschitz in the initial condition, uniformly in
  `t ∈ [-ε, ε]`. -/
theorem exists_uniform_chart_geodesic_family (g : RiemannianMetric I M)
    [I.Boundaryless] [CompleteSpace E] (p : M) (v : TangentSpace I p) :
    ∃ ε > 0, ∃ V₁ ∈ 𝓝 p, ∃ V₂ ∈ 𝓝 (v : E), ∃ c : M → E → ℝ → M,
      ∃ (r : ℝ) (Z : E × E → ℝ → E × E) (L : ℝ≥0), 0 < r ∧
      (∀ q ∈ V₁, ∀ w ∈ V₂, ((extChartAt I p q, w) : E × E) ∈
        closedBall ((extChartAt I p p, (v : E)) : E × E) r) ∧
      (∀ q ∈ V₁, ∀ w ∈ V₂,
        IsChartGeodesicOn (I := I) g p (c q w) (Ioo (-ε) ε) ∧
        c q w 0 = q ∧
        HasDerivAt (fun s => extChartAt I p (c q w s)) w 0) ∧
      (∀ q ∈ V₁, ∀ w ∈ V₂, ∀ t ∈ Icc (-ε) ε,
        extChartAt I p (c q w t) = (Z (extChartAt I p q, w) t).1) ∧
      (∀ q ∈ V₁, ∀ w ∈ V₂, ∀ t ∈ Ioo (-ε) ε,
        deriv (fun s => extChartAt I p (c q w s)) t = (Z (extChartAt I p q, w) t).2) ∧
      (∀ t ∈ Icc (-ε) ε, LipschitzOnWith L (Z · t)
        (closedBall ((extChartAt I p p, (v : E)) : E × E) r)) := by
  classical
  set z₀ : E × E := ((extChartAt I p p, (v : E)) : E × E) with hz₀def
  have hopen : IsOpen ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    (isOpen_extChartAt_target p).prod isOpen_univ
  have hmemz₀ : z₀ ∈ (extChartAt I p).target ×ˢ (univ : Set E) :=
    ⟨mem_extChartAt_target p, mem_univ _⟩
  -- the coordinate spray is `C^1` at the initial condition
  have hC1 : ContDiffAt ℝ 1
      (fun ζ : E × E => Geodesic.geodesicSprayCoord (I := I) g p ζ.1 ζ.2) z₀ :=
    ((Geodesic.contDiffOn_geodesicSprayCoord_prod (I := I) g p).contDiffAt
      (hopen.mem_nhds hmemz₀)).of_le (by norm_num)
  -- Picard–Lindelöf local flow, confined to the chart-target region
  obtain ⟨r, ε, Z, L, hr, hε, hflow, hLip⟩ :=
    exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt hC1
      (hopen.mem_nhds hmemz₀)
  have hrhalf : (0 : ℝ) < r / 2 := by positivity
  -- the neighbourhoods of `p` and `v`
  set V₁ : Set M := (extChartAt I p).source ∩
    extChartAt I p ⁻¹' ball (extChartAt I p p) (r / 2) with hV₁def
  set V₂ : Set E := ball (v : E) (r / 2) with hV₂def
  have hV₁ : V₁ ∈ 𝓝 p :=
    Filter.inter_mem (extChartAt_source_mem_nhds p)
      ((continuousAt_extChartAt p).preimage_mem_nhds (ball_mem_nhds _ hrhalf))
  have hV₂ : V₂ ∈ 𝓝 (v : E) := ball_mem_nhds (α := E) _ hrhalf
  -- initial conditions from `V₁ × V₂` lie in the flow ball
  have hball : ∀ q ∈ V₁, ∀ w ∈ V₂,
      ((extChartAt I p q, w) : E × E) ∈ closedBall z₀ r := by
    intro q hq w hw
    have hq2 : extChartAt I p q ∈ ball (extChartAt I p p) (r / 2) := hq.2
    rw [mem_closedBall, hz₀def, Prod.dist_eq]
    refine max_le ?_ ?_
    · exact (mem_ball.mp hq2).le.trans (by linarith)
    · exact (mem_ball.mp hw).le.trans (by linarith)
  -- the geodesic family: pull the flow's foot back through the chart
  set c : M → E → ℝ → M := fun q w t =>
    (extChartAt I p).symm ((Z (extChartAt I p q, w) t).1) with hcdef
  refine ⟨ε, hε, V₁, hV₁, V₂, hV₂, c, r, Z, L, hr, hball, ?_, ?_, ?_, hLip⟩
  · -- the geodesic clauses, one initial condition at a time
    intro q hq w hw
    obtain ⟨h0, hd, hmem⟩ := hflow _ (hball q hq w hw)
    have htarget : ∀ s ∈ Icc (-ε) ε,
        (Z (extChartAt I p q, w) s).1 ∈ (extChartAt I p).target :=
      fun s hs => (hmem s hs).1
    have hu_eq : ∀ s ∈ Icc (-ε) ε,
        extChartAt I p (c q w s) = (Z (extChartAt I p q, w) s).1 :=
      fun s hs => (extChartAt I p).right_inv (htarget s hs)
    -- the flow line solves the spray ODE on the open interval
    have hZd : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (Z (extChartAt I p q, w))
        (Geodesic.geodesicSprayCoord (I := I) g p
          (Z (extChartAt I p q, w) t).1 (Z (extChartAt I p q, w) t).2) t :=
      fun t ht => (hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    -- componentwise derivatives of the flow line
    have huZd : ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (fun s => (Z (extChartAt I p q, w) s).1)
          ((Z (extChartAt I p q, w) t).2) t := by
      intro t ht
      have h := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t (hZd t ht)
      exact h
    have hvZd : ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (fun s => (Z (extChartAt I p q, w) s).2)
          (- Geodesic.chartChristoffelContraction (I := I) g p
            (Z (extChartAt I p q, w) t).2 (Z (extChartAt I p q, w) t).2
            (Z (extChartAt I p q, w) t).1) t := by
      intro t ht
      have h := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t (hZd t ht)
      exact h
    -- the chart reading of `c q w` agrees with the flow's foot near each interior time
    have hu_ev : ∀ t ∈ Ioo (-ε) ε,
        (fun s => extChartAt I p (c q w s)) =ᶠ[𝓝 t]
          fun s => (Z (extChartAt I p q, w) s).1 := by
      intro t ht
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hu_eq s (Ioo_subset_Icc_self hs)
    have hud : ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (fun s => extChartAt I p (c q w s))
          ((Z (extChartAt I p q, w) t).2) t :=
      fun t ht => (huZd t ht).congr_of_eventuallyEq (hu_ev t ht)
    have hderiv_eq : ∀ t ∈ Ioo (-ε) ε,
        deriv (fun s => extChartAt I p (c q w s)) t
          = (Z (extChartAt I p q, w) t).2 :=
      fun t ht => (hud t ht).deriv
    have h0Ioo : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · -- the foot stays in the chart at `p`
      intro t ht
      rw [← extChartAt_source I]
      exact (extChartAt I p).map_target (htarget t (Ioo_subset_Icc_self ht))
    · -- the chart reading is differentiable
      intro t ht
      rw [hderiv_eq t ht]
      exact hud t ht
    · -- the chart velocity solves the Christoffel equation
      intro t ht
      have hev : deriv (fun s => extChartAt I p (c q w s)) =ᶠ[𝓝 t]
          fun s => (Z (extChartAt I p q, w) s).2 := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
        exact hderiv_eq s hs
      have hvd := (hvZd t ht).congr_of_eventuallyEq hev
      rw [hderiv_eq t ht, hu_eq t (Ioo_subset_Icc_self ht)]
      exact hvd
    · -- initial position
      have h1 : (Z (extChartAt I p q, w) 0).1 = extChartAt I p q := by rw [h0]
      show (extChartAt I p).symm ((Z (extChartAt I p q, w) 0).1) = q
      rw [h1]
      exact (extChartAt I p).left_inv hq.1
    · -- initial velocity
      have h2 : (Z (extChartAt I p q, w) 0).2 = w := by rw [h0]
      have h := hud 0 h0Ioo
      rwa [h2] at h
  · -- the chart reading is computed by the flow
    intro q hq w hw t ht
    obtain ⟨-, -, hmem⟩ := hflow _ (hball q hq w hw)
    exact (extChartAt I p).right_inv (hmem t ht).1
  · -- the chart velocity is computed by the flow
    intro q hq w hw t ht
    obtain ⟨-, hd, hmem⟩ := hflow _ (hball q hq w hw)
    have htarget : ∀ s ∈ Icc (-ε) ε,
        (Z (extChartAt I p q, w) s).1 ∈ (extChartAt I p).target :=
      fun s hs => (hmem s hs).1
    have hZd : HasDerivAt (Z (extChartAt I p q, w))
        (Geodesic.geodesicSprayCoord (I := I) g p
          (Z (extChartAt I p q, w) t).1 (Z (extChartAt I p q, w) t).2) t :=
      (hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have huZd : HasDerivAt (fun s => (Z (extChartAt I p q, w) s).1)
        ((Z (extChartAt I p q, w) t).2) t := by
      have h := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t hZd
      exact h
    have hu_ev : (fun s => extChartAt I p (c q w s)) =ᶠ[𝓝 t]
        fun s => (Z (extChartAt I p q, w) s).1 := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact (extChartAt I p).right_inv (htarget s (Ioo_subset_Icc_self hs))
    exact (huZd.congr_of_eventuallyEq hu_ev).deriv

/-- **Math.** **Local existence of geodesics** (Petersen Theorem 5.2.3). For
every `p : M` and initial velocity `v ∈ T_pM` there are `ε > 0`,
neighbourhoods `V₁` of `p` and `V₂` of `v` (in chart coordinates), and a
family `c` of geodesics in the chart at `p`, defined on `(-ε, ε)` for **all**
initial conditions `(q, w) ∈ V₁ × V₂`, with `c q w 0 = q` and initial chart
velocity `w`. The final conjunct is Petersen's clause that
`(q, w, t) ↦ c_{q,w}(t)` is jointly `C^∞`, read in chart coordinates; smooth
dependence of ODE solutions on initial conditions is not yet available in
mathlib, so that one conjunct is left as a documented `sorry` (see
`geodesic_local_existence_lipschitz` for a sorry-free variant with Lipschitz
dependence instead). -/
theorem geodesic_local_existence (g : RiemannianMetric I M) [I.Boundaryless] [CompleteSpace E]
    (p : M) (v : TangentSpace I p) :
    ∃ ε > 0, ∃ V₁ ∈ 𝓝 p, ∃ V₂ ∈ 𝓝 (v : E), ∃ c : M → E → ℝ → M,
      (∀ q ∈ V₁, ∀ w ∈ V₂,
        IsChartGeodesicOn (I := I) g p (c q w) (Ioo (-ε) ε) ∧
        c q w 0 = q ∧
        HasDerivAt (fun s => extChartAt I p (c q w s)) w 0) ∧
      ContDiffOn ℝ ∞
        (fun xwt : (E × E) × ℝ =>
          extChartAt I p (c ((extChartAt I p).symm xwt.1.1) xwt.1.2 xwt.2))
        (((extChartAt I p '' V₁) ×ˢ V₂) ×ˢ Ioo (-ε) ε) := by
  obtain ⟨ε, hε, V₁, hV₁, V₂, hV₂, c, r, Z, L, hr, hball, hfam, hread, -, hLip⟩ :=
    exists_uniform_chart_geodesic_family (I := I) g p v
  refine ⟨ε, hε, V₁, hV₁, V₂, hV₂, c, hfam, ?_⟩
  -- Smooth dependence of ODE solutions on initial conditions is not yet in
  -- mathlib (only Lipschitz dependence via Gronwall). Blocked: this is the
  -- C^∞ clause of Petersen Thm 5.2.3.
  sorry

/-- **Math.** **Local existence of geodesics, with Lipschitz dependence on the
initial data** (Petersen Theorem 5.2.3, with the `C^∞`-dependence clause
replaced by the quantitative dependence mathlib's Grönwall theory provides).
The family `c` of chart geodesics of `geodesic_local_existence` can be chosen
so that, uniformly for `t ∈ [-ε, ε]`, the chart position `φ_p(c q w t)` is
`L`-Lipschitz in the chart initial data `(φ_p(q), w)`. This statement is fully
proven (no `sorry`). -/
theorem geodesic_local_existence_lipschitz (g : RiemannianMetric I M) [I.Boundaryless]
    [CompleteSpace E] (p : M) (v : TangentSpace I p) :
    ∃ ε > 0, ∃ V₁ ∈ 𝓝 p, ∃ V₂ ∈ 𝓝 (v : E), ∃ c : M → E → ℝ → M, ∃ L : ℝ≥0,
      (∀ q ∈ V₁, ∀ w ∈ V₂,
        IsChartGeodesicOn (I := I) g p (c q w) (Ioo (-ε) ε) ∧
        c q w 0 = q ∧
        HasDerivAt (fun s => extChartAt I p (c q w s)) w 0) ∧
      (∀ t ∈ Icc (-ε) ε, ∀ q ∈ V₁, ∀ q' ∈ V₁, ∀ w ∈ V₂, ∀ w' ∈ V₂,
        dist (extChartAt I p (c q w t)) (extChartAt I p (c q' w' t)) ≤
          L * dist ((extChartAt I p q, w) : E × E) ((extChartAt I p q', w') : E × E)) := by
  obtain ⟨ε, hε, V₁, hV₁, V₂, hV₂, c, r, Z, L, hr, hball, hfam, hread, -, hLip⟩ :=
    exists_uniform_chart_geodesic_family (I := I) g p v
  refine ⟨ε, hε, V₁, hV₁, V₂, hV₂, c, L, hfam, ?_⟩
  intro t ht q hq q' hq' w hw w' hw'
  rw [hread q hq w hw t ht, hread q' hq' w' hw' t ht]
  calc dist ((Z (extChartAt I p q, w) t).1) ((Z (extChartAt I p q', w') t).1)
      ≤ dist (Z (extChartAt I p q, w) t) (Z (extChartAt I p q', w') t) := by
        rw [Prod.dist_eq]; exact le_max_left _ _
    _ ≤ L * dist ((extChartAt I p q, w) : E × E) ((extChartAt I p q', w') : E × E) :=
        (hLip t ht).dist_le_mul _ (hball q hq w hw) _ (hball q' hq' w' hw')

end PetersenLib
