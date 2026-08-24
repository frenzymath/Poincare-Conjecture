import MorganTianLib.Ch01.ExpJacobiDensity
import MorganTianLib.Ch01.MetricEuclideanEquiv
import MorganTianLib.Ch01.BishopGromovBall

/-!
# Poincaré Ch. 1, §1.4 — Bishop–Gromov on the manifold: assembling `hanti`

`BishopGromovBall.bishop_gromov_ball` proves the relative volume comparison for the abstract
`expBallVolume` of any density `ρ` whose polar ratio `ν_ω(t)/sn_k(t)^{n-1}` is non-increasing in
every unit direction `ω`.  `MetricEuclideanEquiv.riemannianMeasure_ball_eq_expBallVolume`
identifies `μ_g(B(p,r))` with `expBallVolume volume ρ̃ r` for the transported Jacobian `ρ̃`.  What
remains for `thm:bishop-gromov` on the manifold is to *discharge* `hanti` for `ρ̃`.

This file collects that assembly.  The two building blocks are:

* `antitoneOn_Ioo_of_eventually_zero` — the **antitone-across-cut** principle: a density that is
  antitone-nonneg up to the cut radius `r₀` and *zero* beyond it (which `ρ̃` is, being extended by
  `0` past the cut) is antitone on all of `(0, R)`.  The value drops to `0` at the cut, and `0` is
  `≤` every earlier value, so monotonicity survives the truncation.
* `metricInner_gpEuclideanEquiv_self_of_mem_sphere` — a unit direction `ω ∈ S ⊆ 𝔼` transports under
  the `g_p`-isometry `L = gpEuclideanEquiv` to a `g`-unit vector `u = L ω`, so
  `expRiemannianJacobian_polarDensity_of_minimizing` (the single-datum radial comparison) applies
  along `γ_u`.

Blueprint: `thm:bishop-gromov`.
-/

open Set Filter Riemannian Module MeasureTheory
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace ENNReal

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]
  [CompleteSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ### The antitone-across-cut principle -/

/-- **Math.** **Truncation preserves monotonicity of a nonnegative antitone density.**  If `F` is
non-increasing and `≥ 0` on `(0, r₀)`, and `F = 0` on `[r₀, R)`, then `F` is non-increasing on all
of `(0, R)`.  This is the step that lets Bishop–Gromov integrate a density that is cut off at the
cut locus: past the cut the polar density is `0`, and `0` is `≤` every value it took before, so the
ratio stays non-increasing across the cut. -/
theorem antitoneOn_Ioo_of_eventually_zero {F : ℝ → ℝ} {r₀ R : ℝ}
    (hanti : AntitoneOn F (Ioo 0 r₀))
    (hnonneg : ∀ t ∈ Ioo (0 : ℝ) r₀, 0 ≤ F t)
    (hzero : ∀ t ∈ Ico r₀ R, F t = 0) :
    AntitoneOn F (Ioo 0 R) := by
  intro s hs t ht hst
  rcases lt_or_ge s r₀ with hsr | hsr
  · rcases lt_or_ge t r₀ with htr | htr
    · exact hanti ⟨hs.1, hsr⟩ ⟨ht.1, htr⟩ hst
    · rw [hzero t ⟨htr, ht.2⟩]
      exact hnonneg s ⟨hs.1, hsr⟩
  · rw [hzero t ⟨hsr.trans hst, ht.2⟩, hzero s ⟨hsr, hs.2⟩]

/-! ### Unit directions transport to `g`-unit vectors -/

/-- **Math.** A Euclidean unit vector `ω ∈ S ⊆ 𝔼` transports under the `g_p`-isometry
`L = gpEuclideanEquiv` to a `g`-unit vector: `g_p(Lω, Lω) = ⟪ω,ω⟫ = ‖ω‖² = 1`. -/
theorem metricInner_gpEuclideanEquiv_self_of_mem_sphere
    (g : RiemannianMetric I M) (p : M) {w : 𝔼} (hw : w ∈ Metric.sphere (0 : 𝔼) 1) :
    g.metricInner p
      ((gpEuclideanEquiv (I := I) g p w : TangentSpace I p))
      (gpEuclideanEquiv (I := I) g p w) = 1 := by
  rw [gpEuclideanEquiv_metricInner (I := I) g p w w, real_inner_self_eq_norm_sq]
  rw [mem_sphere_zero_iff_norm] at hw
  rw [hw]; norm_num

/-- **Math.** `expRiemannianJacobian` is a genuine density: `ρ_p(v) = |det| · √det g ≥ 0`. -/
theorem expRiemannianJacobian_nonneg (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : E) : 0 ≤ expRiemannianJacobian (I := I) g hg p v := by
  rw [expRiemannianJacobian]
  exact mul_nonneg (abs_nonneg _) (chartVolumeDensity_nonneg (I := I) g _ _)

/-- **Math.** The transported Jacobian is nonnegative (indicator of a nonnegative density). -/
theorem transportedJacobian_nonneg (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (x : 𝔼) : 0 ≤ transportedJacobian (I := I) g hg p x := by
  rw [transportedJacobian]
  exact Set.indicator_nonneg (fun y _ => expRiemannianJacobian_nonneg (I := I) g hg p _) x

/-! ### The per-direction antitone ratio for the transported Jacobian -/

/-- **Math.** **`thm:bishop-gromov`, `hanti` in one direction.**  For a Euclidean unit direction
`w`, the polar density of the transported Jacobian `ρ̃`, divided by the model density
`sn_k^{n-1}`, is non-increasing on `(0, R)`.

Writing `u = L w` (a `g`-unit vector) and `c = cutTime(u)`, the density is
`√det g_p · polarDensity 𝒥` up to the clamped cut radius `r₀ = min(R, c)` — antitone there by the
single-datum radial comparison `expRiemannianJacobian_polarDensity_of_minimizing` — and `0` beyond
it, `ρ̃` being extended by `0` past the cut.  `antitoneOn_Ioo_of_eventually_zero` glues the two.

The Ricci hypothesis is the manifold-wide lower bound `Ric ≥ −(n−1)k` on the closed ball; it is
specialised along `γ_u` at unit speed, where `d(p, γ_u(s)) ≤ s ≤ r₀ ≤ R` keeps `γ_u(s)` in the
ball.

Blueprint: `thm:bishop-gromov`. -/
theorem antitoneOn_ratio_transportedJacobian
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p : M) {k R : ℝ} (hk : 0 ≤ k) (hR : 0 < R) (hdim : 2 ≤ Module.finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    (hric : ∀ x ∈ Metric.closedBall p R, ∀ v : TangentSpace I x,
      -(((Module.finrank ℝ E : ℝ) - 1) * k) * g.metricInner x v v
        ≤ ricciAt g g.leviCivitaConnection hLC x v v)
    {w : 𝔼} (hw : w ∈ Metric.sphere (0 : 𝔼) 1) :
    AntitoneOn (fun t => t ^ (Module.finrank ℝ E - 1)
        * transportedJacobian (I := I) g hg p (t • w)
        / snK k t ^ (Module.finrank ℝ E - 1)) (Ioo 0 R) := by
  classical
  have hu : g.metricInner p
      ((gpEuclideanEquiv (I := I) g p w : E) : TangentSpace I p)
      (gpEuclideanEquiv (I := I) g p w) = 1 :=
    metricInner_gpEuclideanEquiv_self_of_mem_sphere (I := I) g p hw
  set u : E := gpEuclideanEquiv (I := I) g p w with hu_def
  -- `L (t • w) = t • u`
  have hLtw : ∀ t : ℝ, gpEuclideanEquiv (I := I) g p (t • w) = t • u := by
    intro t; rw [map_smul, hu_def]
  -- the density value at `t • w`, split by the cut condition
  have hval1 : ∀ t : ℝ, 1 < cutTime (I := I) g hg p ((t • u : E) : TangentSpace I p) →
      transportedJacobian (I := I) g hg p (t • w) = expRiemannianJacobian (I := I) g hg p (t • u) := by
    intro t ht
    have hmem : (t • w : 𝔼) ∈
        {y : 𝔼 | 1 < cutTime (I := I) g hg p (gpEuclideanEquiv (I := I) g p y)} := by
      rw [Set.mem_setOf_eq, hLtw]; exact ht
    rw [transportedJacobian, Set.indicator_of_mem hmem, hLtw]
  have hval0 : ∀ t : ℝ, ¬ 1 < cutTime (I := I) g hg p ((t • u : E) : TangentSpace I p) →
      transportedJacobian (I := I) g hg p (t • w) = 0 := by
    intro t ht
    have hmem : (t • w : 𝔼) ∉
        {y : 𝔼 | 1 < cutTime (I := I) g hg p (gpEuclideanEquiv (I := I) g p y)} := by
      rw [Set.mem_setOf_eq, hLtw]; exact ht
    rw [transportedJacobian, Set.indicator_of_notMem hmem]
  -- unit speed of `γ_u`
  have hspeedAll : ∀ t : ℝ,
      g.metricInner (globalGeodesic (I := I) g hg p (u : TangentSpace I p) t)
        (mfderivVelocity (I := I) (E := E) (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) t)
        (mfderivVelocity (I := I) (E := E) (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) t)
        = 1 := by
    have hspeed0 : Geodesic.speedSq (I := I) g
        (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) 0 = 1 := by
      rw [speedSq_globalGeodesic g hg p (u : TangentSpace I p), hu]
    intro t
    show Geodesic.speedSq (I := I) g (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) t = 1
    rw [← hspeed0]
    exact IsGeodesicOn.speedSq_eq (I := I)
      ((isGeodesic_globalGeodesic g hg p (u : TangentSpace I p)).isGeodesicOn univ) isOpen_univ
      isPreconnected_univ (continuous_globalGeodesic g hg p (u : TangentSpace I p)).continuousOn
      (mem_univ t) (mem_univ 0)
  -- the clamped cut radius
  set c : ℝ≥0∞ := cutTime (I := I) g hg p (u : TangentSpace I p) with hc_def
  set r₀ : ℝ := (min (ENNReal.ofReal R) c).toReal with hr₀_def
  have hmin_ne_top : min (ENNReal.ofReal R) c ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)
  have hofReal_r₀ : ENNReal.ofReal r₀ = min (ENNReal.ofReal R) c :=
    ENNReal.ofReal_toReal hmin_ne_top
  have hr₀0 : 0 ≤ r₀ := ENNReal.toReal_nonneg
  have hr₀R : r₀ ≤ R := by
    rw [hr₀_def]
    refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top (min_le_left _ _)) ?_
    rw [ENNReal.toReal_ofReal hR.le]
  have hr₀_le_c : ENNReal.ofReal r₀ ≤ c := by rw [hofReal_r₀]; exact min_le_right _ _
  -- `hzero`: past the clamped cut radius the density vanishes
  have hzero : ∀ t ∈ Ico r₀ R,
      t ^ (Module.finrank ℝ E - 1) * transportedJacobian (I := I) g hg p (t • w)
        / snK k t ^ (Module.finrank ℝ E - 1) = 0 := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hr₀0 ht.1
    suffices h : t ^ (Module.finrank ℝ E - 1) * transportedJacobian (I := I) g hg p (t • w) = 0 by
      rw [h, zero_div]
    rcases eq_or_lt_of_le ht0 with h0 | h0
    · rw [← h0, zero_pow (by omega), zero_mul]
    · -- `t > 0`: the cut condition fails, so the density is `0`
      have hcle : c < ENNReal.ofReal R := by
        have hlt : ENNReal.ofReal r₀ < ENNReal.ofReal R := by
          rw [ENNReal.ofReal_lt_ofReal_iff hR]; exact lt_of_le_of_lt ht.1 ht.2
        rw [hofReal_r₀] at hlt
        rcases min_cases (ENNReal.ofReal R) c with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he] at hlt; exact absurd hlt (lt_irrefl _)
        · rw [he] at hlt; exact hlt
      have hc_eq : c = ENNReal.ofReal r₀ := by
        rw [hofReal_r₀, min_eq_right hcle.le]
      have hnotcut : ¬ 1 < cutTime (I := I) g hg p ((t • u : E) : TangentSpace I p) := by
        rw [not_lt]
        have hct : cutTime (I := I) g hg p ((t • u : E) : TangentSpace I p)
            = ENNReal.ofReal (r₀ / t) := by
          have := cutTime_smul (I := I) g hg p (u : TangentSpace I p) h0 hr₀0 hc_eq
          change cutTime (I := I) g hg p (t • (u : TangentSpace I p))
            = ENNReal.ofReal (r₀ / t)
          exact this
        rw [hct]
        calc ENNReal.ofReal (r₀ / t) ≤ ENNReal.ofReal 1 := by
              rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)]
              rw [div_le_one h0]; exact ht.1
          _ = 1 := by simp
      rw [hval0 t hnotcut, mul_zero]
  -- split on whether the pre-cut region is nonempty
  rcases (lt_or_ge 0 r₀).symm with hr₀le | hr₀pos
  · -- `r₀ = 0`: density is `0` on all of `(0, R)`
    have hr₀eq : r₀ = 0 := le_antisymm hr₀le hr₀0
    refine antitoneOn_Ioo_of_eventually_zero ?_ ?_ hzero
    · rw [hr₀eq]; intro a ha; rw [Set.Ioo_self] at ha; exact ha.elim
    · rw [hr₀eq]; intro a ha; rw [Set.Ioo_self] at ha; exact ha.elim
  · -- `0 < r₀`: pre-cut antitone by the radial comparison, then glue
    have hminr₀ : IsMinimizingUpTo (I := I) g hg p (u : TangentSpace I p) r₀ :=
      (le_cutTime_iff (I := I) g hg p (u : TangentSpace I p) hr₀0).1 hr₀_le_c
    have hmin : ∀ s ∈ Ioo (0 : ℝ) r₀,
        s ≤ dist p (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s) := by
      intro s hs
      have hmins : IsMinimizingUpTo (I := I) g hg p (u : TangentSpace I p) s :=
        IsMinimizingUpTo.mono g hg p _ hminr₀ hs.1.le hs.2.le
      rw [IsMinimizingUpTo, hu, Real.sqrt_one, one_mul] at hmins
      exact hmins.ge
    have hricγ : ∀ s ∈ Icc (0 : ℝ) r₀,
        -(((Module.finrank ℝ E : ℝ) - 1) * k)
          ≤ ricciAt g g.leviCivitaConnection hLC
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s)
              (mfderivVelocity (I := I) (E := E)
                (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s)
              (mfderivVelocity (I := I) (E := E)
                (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s) := by
      intro s hs
      have hmem : globalGeodesic (I := I) g hg p (u : TangentSpace I p) s ∈
          Metric.closedBall p R := by
        rw [Metric.mem_closedBall, dist_comm]
        calc dist p (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s)
              ≤ Real.sqrt (g.metricInner p (u : TangentSpace I p) u) * s :=
              dist_globalGeodesic_zero_le (I := I) g hg p (u : TangentSpace I p) hs.1
          _ = s := by rw [hu, Real.sqrt_one, one_mul]
          _ ≤ R := le_trans hs.2 hr₀R
      have hspec := hric _ hmem
        (mfderivVelocity (I := I) (E := E)
          (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s)
      rwa [hspeedAll s, mul_one] at hspec
    obtain ⟨e, 𝒥, 𝒥', C, hRJ, hanti_inner, _hlim, _hpos, hdensity⟩ :=
      expRiemannianJacobian_polarDensity_of_minimizing (I := I) g hg p hk hr₀pos hdim hLC hu
        hmin hricγ
    -- on the pre-cut region the ratio is `√det g_p ·` (an antitone ratio)
    have hval_pre : ∀ t ∈ Ioo (0 : ℝ) r₀,
        t ^ (Module.finrank ℝ E - 1) * transportedJacobian (I := I) g hg p (t • w)
          / snK k t ^ (Module.finrank ℝ E - 1)
        = Real.sqrt ((chartGramMatrix (I := I) g p p).det)
            * (polarDensity 𝒥 t / snK k t ^ (Module.finrank ℝ E - 1)) := by
      intro t ht
      -- the cut condition holds on `(0, r₀)`
      have hcut : 1 < cutTime (I := I) g hg p ((t • u : E) : TangentSpace I p) := by
        have hmimg : IsMinimizingUpTo (I := I) g hg p ((t • u : E) : TangentSpace I p) (r₀ / t) := by
          let v : TangentSpace I p := (u : TangentSpace I p)
          change IsMinimizingUpTo (I := I) g hg p (t • v) (r₀ / t)
          rw [isMinimizingUpTo_smul (I := I) g hg p v ht.1,
            mul_div_cancel₀ r₀ (ne_of_gt ht.1)]
          exact hminr₀
        have hle : ENNReal.ofReal (r₀ / t)
            ≤ cutTime (I := I) g hg p ((t • u : E) : TangentSpace I p) :=
          le_cutTime (I := I) g hg p _ ⟨(div_pos hr₀pos ht.1).le, hmimg⟩
        refine lt_of_lt_of_le ?_ hle
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp, ENNReal.ofReal_lt_ofReal_iff]
        · rw [lt_div_iff₀ ht.1, one_mul]; exact ht.2
        · rw [div_pos_iff]; exact Or.inl ⟨hr₀pos, ht.1⟩
      rw [hval1 t hcut, hdensity t ht]
      have htne : t ≠ 0 := ne_of_gt ht.1
      have htpow : t ^ (Module.finrank ℝ E - 1) ≠ 0 := pow_ne_zero _ htne
      field_simp
    -- assemble via the truncation principle
    refine antitoneOn_Ioo_of_eventually_zero ?_ ?_ hzero
    · -- pre-cut antitone: `√det g_p ·` antitone
      intro s hs t ht hst
      simp only [hval_pre s hs, hval_pre t ht]
      exact mul_le_mul_of_nonneg_left (hanti_inner hs ht hst) (Real.sqrt_nonneg _)
    · -- pre-cut nonnegativity
      intro t ht
      rw [hval_pre t ht]
      exact mul_nonneg (Real.sqrt_nonneg _)
        (div_nonneg (le_of_lt (_hpos t ht)) (pow_nonneg (snK_nonneg k t hk ht.1.le) _))

/-! ### The manifold-level relative volume comparison -/

/-- **Math.** **Bishop--Gromov on the actual manifold.**  For a complete connected Riemannian
manifold, a point `p`, and a ball with compact closure, a Ricci lower bound on that ball implies
that the ratio of the *actual Riemannian ball volume* to the model ball volume is non-increasing.

The only analytic side condition exposed here is measurability of the transported exponential
Jacobian.  This is deliberately a producer obligation rather than an assumed radial comparison:
`antitoneOn_ratio_transportedJacobian` derives the latter from the Ricci bound and minimality.
The compact-closure hypothesis is retained in the source-faithful statement (the current global
geodesic infrastructure also assumes completeness). -/
theorem bishop_gromov_manifold_ratio
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (p : M) {k R : ℝ} (hk : 0 ≤ k) (hR : 0 < R)
    (_hcompact : IsCompact (closure (Metric.ball p R)))
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    (hric : ∀ x ∈ Metric.closedBall p R, ∀ v : TangentSpace I x,
      -(((Module.finrank ℝ E : ℝ) - 1) * k) * g.metricInner x v v
        ≤ ricciAt g g.leviCivitaConnection hLC x v v)
    (hjac : Measurable (transportedJacobian (I := I) g hg p)) :
    AntitoneOn
      (fun r =>
        riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r) /
          modelBallVolume (volume : Measure 𝔼) k r)
      (Ioo 0 R) := by
  intro r₁ hr₁ r₂ hr₂ h₁₂
  change
    riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r₂) /
        modelBallVolume (volume : Measure 𝔼) k r₂ ≤
      riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r₁) /
        modelBallVolume (volume : Measure 𝔼) k r₁
  rw [riemannianMeasure_ball_eq_expBallVolume (I := I) g hg p r₁,
    riemannianMeasure_ball_eq_expBallVolume (I := I) g hg p r₂]
  exact (bishop_gromov_ball_ratio (μ := (volume : Measure 𝔼)) (E := 𝔼) (k := k) (R := R)
    hjac (transportedJacobian_nonneg (I := I) g hg p) hk (by
      intro w hw
      simpa only [polarBallDensity, finrank_coeffSpace (E := E)] using
        (antitoneOn_ratio_transportedJacobian (I := I) g hg p hk hR hdim hLC hric hw)))
    hr₁ hr₂ h₁₂

/-! ### Explicit producer obligations for the remaining source clauses -/

/-- **Math.** The origin density of the transported exponential chart relative to the fixed
`gpHaar = L_*volume` convention.  `MetricEuclideanEquiv` identifies this with
`ENNReal.ofReal (sqrt (det (chartGramMatrix g p p)))`; it is the small-radius limit of the
unscaled actual/model volume ratio.  A normalized Riemannian-measure convention makes this
constant equal to `1` (equivalently, one may scale `gpHaar` by its inverse). -/
def gpHaarOriginDensity (g : RiemannianMetric I M) (p : M) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt ((chartGramMatrix (I := I) g p p).det))

/-- **Math.** The current library has all ingredients for the manifold ratio monotonicity, but does not yet
contain the final small-radius integration theorem or the geometric identification of the flat
model integral with a multiple of `r^n`.  This record names those exact missing producers.  Keeping
them explicit makes the node conditional/not-ready instead of hiding either gap behind an
abstract `hanti` assumption.  The normalization producer records the honest limit for the fixed
`gpHaar` convention, namely `gpHaarOriginDensity`, rather than silently asserting that it is `1`.
The source normalization is recovered below only under the explicit chart-normalization hypothesis
that this constant is `1`; with the fixed `gpHaar` definition, a general normalization would
instead use the scaled measure `C_p⁻¹ • gpHaar`. -/
structure BishopGromovManifoldProducers
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M] (p : M)
    (R : ℝ) : Prop where
  transportedJacobian_measurable :
    Measurable (transportedJacobian (I := I) g hg p)
  small_radius_normalization :
    Tendsto
      (fun r =>
        riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r) /
          modelBallVolume (volume : Measure 𝔼) 0 r)
      (𝓝[>] (0 : ℝ)) (𝓝 (gpHaarOriginDensity (I := I) g p))
  flat_model_power_identification :
    ∃ C : ℝ≥0∞, 0 < C ∧ C ≠ ⊤ ∧
      ∀ r ∈ Ioo (0 : ℝ) R,
        modelBallVolume (volume : Measure 𝔼) 0 r = C * ENNReal.ofReal (r ^ Module.finrank ℝ E)

/-- **Math.** Conditional packaging of the source theorem's normalization and `k=0` consequence.
The extra hypothesis `hCnorm` is the explicit chart-normalization condition
`gpHaarOriginDensity = 1`; with the fixed `gpHaar` definition this is not an implicit rescaling.
Without it the producer exposes the corresponding `gpHaarOriginDensity` limit instead. -/
theorem bishop_gromov_manifold_with_producers
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (p : M) {k R : ℝ} (hk : 0 ≤ k) (hR : 0 < R)
    (hcompact : IsCompact (closure (Metric.ball p R)))
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    (hric : ∀ x ∈ Metric.closedBall p R, ∀ v : TangentSpace I x,
      -(((Module.finrank ℝ E : ℝ) - 1) * k) * g.metricInner x v v
        ≤ ricciAt g g.leviCivitaConnection hLC x v v)
    (hric0 : ∀ x ∈ Metric.closedBall p R, ∀ v : TangentSpace I x,
      0 ≤ ricciAt g g.leviCivitaConnection hLC x v v)
    (hCnorm : gpHaarOriginDensity (I := I) g p = 1)
    (hprod : BishopGromovManifoldProducers (I := I) g hg p R) :
    AntitoneOn
      (fun r =>
        riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r) /
          modelBallVolume (volume : Measure 𝔼) k r)
      (Ioo 0 R) ∧
    Tendsto
      (fun r =>
        riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r) /
          modelBallVolume (volume : Measure 𝔼) 0 r)
      (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
    AntitoneOn
      (fun r =>
        riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r) /
          ENNReal.ofReal (r ^ Module.finrank ℝ E))
      (Ioo 0 R) := by
  have hratio := bishop_gromov_manifold_ratio (I := I) g hg p hk hR hcompact hdim hLC hric
      hprod.transportedJacobian_measurable
  have hratio0 := bishop_gromov_manifold_ratio (I := I) g hg p (k := 0) (by norm_num) hR hcompact
      hdim hLC (by
        intro x hx v
        simpa using hric0 x hx v) hprod.transportedJacobian_measurable
  rcases hprod.flat_model_power_identification with ⟨C, hCpos, hCtop, hCeq⟩
  have hC0 : C ≠ 0 := ne_of_gt hCpos
  have hsmall := hprod.small_radius_normalization
  rw [hCnorm] at hsmall
  refine ⟨hratio, hsmall, ?_⟩
  intro r₁ hr₁ r₂ hr₂ h₁₂
  have hbase := hratio0 hr₁ hr₂ h₁₂
  change
    riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r₂) /
        modelBallVolume (volume : Measure 𝔼) 0 r₂ ≤
      riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r₁) /
        modelBallVolume (volume : Measure 𝔼) 0 r₁ at hbase
  have hP₁pos : 0 < ENNReal.ofReal (r₁ ^ Module.finrank ℝ E) :=
    ENNReal.ofReal_pos.mpr (pow_pos hr₁.1 _)
  have hP₂pos : 0 < ENNReal.ofReal (r₂ ^ Module.finrank ℝ E) :=
    ENNReal.ofReal_pos.mpr (pow_pos hr₂.1 _)
  have hP₁0 : ENNReal.ofReal (r₁ ^ Module.finrank ℝ E) ≠ 0 := ne_of_gt hP₁pos
  have hP₂0 : ENNReal.ofReal (r₂ ^ Module.finrank ℝ E) ≠ 0 := ne_of_gt hP₂pos
  have hP₁top : ENNReal.ofReal (r₁ ^ Module.finrank ℝ E) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hP₂top : ENNReal.ofReal (r₂ ^ Module.finrank ℝ E) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hrewrite₁ :
      riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r₁) /
          (C * ENNReal.ofReal (r₁ ^ Module.finrank ℝ E)) =
        (riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r₁) /
          ENNReal.ofReal (r₁ ^ Module.finrank ℝ E)) / C := by
    calc
      _ = riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r₁) * 1 /
          (ENNReal.ofReal (r₁ ^ Module.finrank ℝ E) * C) := by simp [mul_comm]
      _ = riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r₁) /
          ENNReal.ofReal (r₁ ^ Module.finrank ℝ E) * (1 / C) :=
        ENNReal.mul_div_mul_comm (Or.inl hP₁0) (Or.inl hP₁top)
      _ = _ := by simp [div_eq_mul_inv, mul_comm]
  have hrewrite₂ :
      riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r₂) /
          (C * ENNReal.ofReal (r₂ ^ Module.finrank ℝ E)) =
        (riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r₂) /
          ENNReal.ofReal (r₂ ^ Module.finrank ℝ E)) / C := by
    calc
      _ = riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r₂) * 1 /
          (ENNReal.ofReal (r₂ ^ Module.finrank ℝ E) * C) := by simp [mul_comm]
      _ = riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r₂) /
          ENNReal.ofReal (r₂ ^ Module.finrank ℝ E) * (1 / C) :=
        ENNReal.mul_div_mul_comm (Or.inl hP₂0) (Or.inl hP₂top)
      _ = _ := by simp [div_eq_mul_inv, mul_comm]
  rw [hCeq r₁ hr₁, hCeq r₂ hr₂, hrewrite₁, hrewrite₂] at hbase
  have hmul := (ENNReal.le_div_iff_mul_le (Or.inl hC0) (Or.inl hCtop)).mp hbase
  rw [ENNReal.div_mul_cancel hC0 hCtop] at hmul
  exact hmul

end MorganTianLib

end
