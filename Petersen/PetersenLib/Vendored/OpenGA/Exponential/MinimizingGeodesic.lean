/- Vendored from DoCarmo `OpenGALib/Riemannian/Exponential/MinimizingGeodesic.lean`.
   Namespace `Riemannian` mapped to `PetersenLib`; engineering infrastructure only,
   not a blueprint node. -/
import PetersenLib.Vendored.OpenGA.Exponential.MinimizingEqualityManifold
import PetersenLib.Vendored.OpenGA.Exponential.CornerRigidity
import PetersenLib.Vendored.OpenGA.Exponential.RayGeodesic
import PetersenLib.Vendored.OpenGA.Exponential.NormalBallEDist
import PetersenLib.Vendored.OpenGA.Exponential.MinimizingPiecewise
import PetersenLib.Vendored.OpenGA.Geodesic.Completeness
import PetersenLib.Vendored.OpenGA.Geodesic.InitialVelocity
import PetersenLib.Vendored.OpenGA.Geodesic.HopfRinow.EVariationLePathELength

/-!
# Minimizing curves are geodesics (do Carmo Ch. 3, Corollary 3.9)

do Carmo, *Riemannian Geometry*, Ch. 3, Corollary 3.9: a piecewise
differentiable curve, parametrized proportionally to arc length, whose length
does not exceed that of any other piecewise differentiable curve joining its
endpoints, is a geodesic (in particular on the interior of its interval).

Under the standing hypothesis `g.IsRiemannianDist` (the ambient distance is
the Riemannian distance of `g`), "minimizing" is expressed metrically:
`edist (γ a) (γ b) = ℓ(γ)`, since `edist` is the infimum of competitor
lengths.  This is the moving-center localization missing from the
center-anchored equality case (`MinimizingEqualityManifold.lean`), and the
form consumed by the Hopf–Rinow growth induction.

The localization does **not** follow do Carmo's route through totally normal
neighborhoods (a `q`-uniform normal radius); instead it anchors at each
interior time `u` **twice**:

* the forward subsegment from `q = γ u` is short, distance-realizing and
  arclength-proportional, hence *is* the radial geodesic
  `s ↦ exp_q (s • v₂)` by the center-anchored equality case
  (`exists_gauss_equality_geodesic` + the metric normal ball
  `exists_edist_expMap_ball`);
* the time-reversed backward subsegment from `q` likewise traces a radial
  geodesic `s ↦ exp_q (s • v₁)`;
* the two radial legs together realize the distance `2η` between
  `exp_q (η • u₁)` and `exp_q (η • u₂)` for all small `η`, so the corner
  rigidity theorem (`eq_neg_of_forall_edist_expMap_eq`, do Carmo's "a broken
  minimizing curve has no corner") forces `u₂ = -u₁`: near `u` the curve is a
  single exponential ray through `q`, hence satisfies the geodesic equation
  at `u` (`exists_isGeodesicOn_expMap_ray` + locality).

Because each interior time only needs one-sided `C¹` regularity, the same
argument covers the piecewise-`C¹` corollary — corners at the partition
vertices are ruled out by the same rigidity — and the endpoint-anchored
statement do Carmo actually uses in the Hopf–Rinow induction.

## Main statements

* `isGeodesicOn_of_pathELength_arclength_edist` — the `C¹` case: an
  arclength-proportional curve realizing the metric distance between its
  endpoints satisfies the intrinsic geodesic equation on the open interval.
* `isGeodesicOn_of_pathELength_arclength_edist_piecewise` — the
  piecewise-`C¹` case (do Carmo's literal regularity class), on a partition.
* `edist_le_pathELength_piecewise_partition` — the metric lower bound
  `edist ≤ pathELength` across partition vertices.
-/

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

namespace PetersenLib

namespace Exponential

open PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless] [CompleteSpace E]

variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
variable [T2Space (TangentBundle I M')]

/-- **Math.** Subsegment arc length of an arclength-proportional curve: if the
running length from the left endpoint is `ℓ · (t - a)`, then the length of any
subsegment `[s, t]` is `ℓ · (t - s)` (cancellation in the additivity of
`pathELength`). -/
theorem pathELength_segment_of_arclength (g : RiemannianMetric I M')
    {γ : ℝ → M'} {a b ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (harc : letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      ∀ t ∈ Icc a b, Manifold.pathELength I γ a t = ENNReal.ofReal (ℓ * (t - a)))
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    Manifold.pathELength I γ s t = ENNReal.ofReal (ℓ * (t - s)) := by
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  have h1 : Manifold.pathELength I γ a s = ENNReal.ofReal (ℓ * (s - a)) :=
    harc s ⟨has, hst.trans htb⟩
  have h2 : Manifold.pathELength I γ a t = ENNReal.ofReal (ℓ * (t - a)) :=
    harc t ⟨has.trans hst, htb⟩
  have hadd : Manifold.pathELength I γ a t
      = Manifold.pathELength I γ a s + Manifold.pathELength I γ s t :=
    (Manifold.pathELength_add has hst).symm
  have hsplit : ENNReal.ofReal (ℓ * (t - a))
      = ENNReal.ofReal (ℓ * (s - a)) + ENNReal.ofReal (ℓ * (t - s)) := by
    rw [← ENNReal.ofReal_add (mul_nonneg hℓ (by linarith))
      (mul_nonneg hℓ (by linarith))]
    ring_nf
  rw [h1, h2, hsplit] at hadd
  exact ((ENNReal.add_right_inj ENNReal.ofReal_ne_top).mp hadd).symm

/-- **Math.** The metric distance is bounded by the tangent-integral length
across the vertices of a piecewise-`C¹` curve: split at the partition points,
apply the per-piece bound `edist ≤ pathELength`
(`edist_le_pathELength_of_cmdiff`) and the triangle inequality, and telescope
with the additivity of `pathELength`. -/
theorem edist_le_pathELength_piecewise_partition (g : RiemannianMetric I M')
    (hg : g.IsRiemannianDist) {γ : ℝ → M'} {n : ℕ} {τ : ℕ → ℝ}
    (hτ : ∀ i < n, τ i ≤ τ (i + 1))
    (hγ : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc (τ i) (τ (i + 1))))
    {s t : ℝ} (hs : τ 0 ≤ s) (hst : s ≤ t) (ht : t ≤ τ n) :
    letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    edist (γ s) (γ t) ≤ Manifold.pathELength I γ s t := by
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M' := hg
  -- induction over the number of pieces available to the right endpoint
  have key : ∀ m : ℕ, m ≤ n → ∀ s t : ℝ, τ 0 ≤ s → s ≤ t → t ≤ τ m →
      edist (γ s) (γ t) ≤ Manifold.pathELength I γ s t := by
    intro m
    induction m with
    | zero =>
      intro _ s t hs hst ht
      have hts : t = s := le_antisymm (ht.trans hs) hst
      subst hts
      simp
    | succ m ih =>
      intro hmn s t hs hst ht
      have hmn' : m < n := hmn
      rcases le_total t (τ m) with htm | htm
      · exact ih (le_of_lt hmn') s t hs hst htm
      rcases le_total (τ m) s with hsm | hsm
      · -- single piece `[τ m, τ (m+1)]`
        exact OpenGA.HopfRinow.edist_le_pathELength_of_cmdiff
          ((hγ m hmn').mono (Icc_subset_Icc hsm ht)) hst
      · -- split at the vertex `τ m`
        calc edist (γ s) (γ t)
            ≤ edist (γ s) (γ (τ m)) + edist (γ (τ m)) (γ t) :=
              edist_triangle _ _ _
          _ ≤ Manifold.pathELength I γ s (τ m)
              + Manifold.pathELength I γ (τ m) t := by
              gcongr
              · exact ih (le_of_lt hmn') s (τ m) hs hsm le_rfl
              · exact OpenGA.HopfRinow.edist_le_pathELength_of_cmdiff
                  ((hγ m hmn').mono (Icc_subset_Icc le_rfl ht)) htm
          _ = Manifold.pathELength I γ s t :=
              Manifold.pathELength_add hsm htm
  exact key n le_rfl s t hs hst ht

/-- **Math.** Subsegment distance realization: if an arclength-proportional
curve realizes the metric distance between its endpoints, then every
subsegment realizes the distance between *its* endpoints (triangle
inequality + the length upper bound on the two complementary segments).
The `edist ≤ pathELength` upper bound is taken as a hypothesis so that the
same argument serves the `C¹` and the piecewise-`C¹` cases. -/
theorem edist_segment_of_arclength (g : RiemannianMetric I M')
    {γ : ℝ → M'} {a b ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hupper : letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
        edist (γ s) (γ t) ≤ Manifold.pathELength I γ s t)
    (harc : letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      ∀ t ∈ Icc a b, Manifold.pathELength I γ a t = ENNReal.ofReal (ℓ * (t - a)))
    (hmin : edist (γ a) (γ b) = ENNReal.ofReal (ℓ * (b - a)))
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    edist (γ s) (γ t) = ENNReal.ofReal (ℓ * (t - s)) := by
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  have hab : a ≤ b := (has.trans hst).trans htb
  -- upper bound on the subsegment and on the two complements
  have hup : edist (γ s) (γ t) ≤ ENNReal.ofReal (ℓ * (t - s)) := by
    rw [← pathELength_segment_of_arclength (I := I) g hℓ harc has hst htb]
    exact hupper s t has hst htb
  have hup₁ : edist (γ a) (γ s) ≤ ENNReal.ofReal (ℓ * (s - a)) := by
    rw [← pathELength_segment_of_arclength (I := I) g hℓ harc le_rfl has
      (hst.trans htb)]
    exact hupper a s le_rfl has (hst.trans htb)
  have hup₂ : edist (γ t) (γ b) ≤ ENNReal.ofReal (ℓ * (b - t)) := by
    rw [← pathELength_segment_of_arclength (I := I) g hℓ harc (has.trans hst)
      htb le_rfl]
    exact hupper t b (has.trans hst) htb le_rfl
  -- lower bound via the triangle inequality through `γ s` and `γ t`
  have htri : edist (γ a) (γ b)
      ≤ edist (γ a) (γ s) + edist (γ s) (γ t) + edist (γ t) (γ b) :=
    edist_triangle4 _ _ _ _
  have hchain : ENNReal.ofReal (ℓ * (b - a))
      ≤ (ENNReal.ofReal (ℓ * (s - a)) + ENNReal.ofReal (ℓ * (b - t)))
        + edist (γ s) (γ t) := by
    calc ENNReal.ofReal (ℓ * (b - a)) = edist (γ a) (γ b) := hmin.symm
      _ ≤ edist (γ a) (γ s) + edist (γ s) (γ t) + edist (γ t) (γ b) := htri
      _ ≤ ENNReal.ofReal (ℓ * (s - a)) + edist (γ s) (γ t)
          + ENNReal.ofReal (ℓ * (b - t)) := by gcongr
      _ = (ENNReal.ofReal (ℓ * (s - a)) + ENNReal.ofReal (ℓ * (b - t)))
          + edist (γ s) (γ t) := by ring
  have hsplit : ENNReal.ofReal (ℓ * (b - a))
      = (ENNReal.ofReal (ℓ * (s - a)) + ENNReal.ofReal (ℓ * (b - t)))
        + ENNReal.ofReal (ℓ * (t - s)) := by
    rw [← ENNReal.ofReal_add (mul_nonneg hℓ (by linarith))
        (mul_nonneg hℓ (by linarith)),
      ← ENNReal.ofReal_add
        (add_nonneg (mul_nonneg hℓ (by linarith)) (mul_nonneg hℓ (by linarith)))
        (mul_nonneg hℓ (by linarith))]
    ring_nf
  rw [hsplit] at hchain
  have hlow : ENNReal.ofReal (ℓ * (t - s)) ≤ edist (γ s) (γ t) :=
    (ENNReal.add_le_add_iff_left (by
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)).mp
      hchain
  exact le_antisymm hup hlow

/-- **Math.** **The anchored radial identification.** Let `γ` be `C¹`,
arclength-proportional (`pathELength γ t₀ t = ℓ (t - t₀)`) and
distance-realizing (`edist (γ t₀) (γ t) = ℓ (t - t₀)`) on `[t₀, B]`, with
speed `ℓ > 0`.  Then some initial subsegment `[t₀, t₁]` of `γ` is the radial
geodesic of the normal ball at `q = γ t₀`: there is `v ∈ T_qM` with
`|v|_q = ℓ (t₁ - t₀)` and `γ r = exp_q (((r - t₀)/(t₁ - t₀)) • v)` on
`[t₀, t₁]`.

`t₁` is chosen so short that (i) `γ t₁` lies in the metric normal ball of
`q` (`exists_edist_expMap_ball`), producing `v`, and (ii) `‖v‖` is inside
the Gauss radius of the equality case (via the Gram bound of
`exists_le_pathELength`); the distance realization identifies `ℓ(γ|[t₀,t₁])`
with the radial length `√⟨v,v⟩_q`, and the reparametrized subsegment
satisfies the running-length hypothesis of
`exists_gauss_equality_geodesic`. -/
theorem exists_radial_of_anchored (g : RiemannianMetric I M')
    (hg : g.IsRiemannianDist) {γ : ℝ → M'} {t₀ B ℓ : ℝ} {q : M'}
    (hq : γ t₀ = q) (ht₀B : t₀ < B) (hℓ : 0 < ℓ)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc t₀ B))
    (harc : letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      ∀ t ∈ Icc t₀ B, Manifold.pathELength I γ t₀ t
        = ENNReal.ofReal (ℓ * (t - t₀)))
    (hedist : ∀ t ∈ Icc t₀ B, edist (γ t₀) (γ t)
      = ENNReal.ofReal (ℓ * (t - t₀))) :
    ∃ t₁ : ℝ, t₀ < t₁ ∧ t₁ ≤ B ∧ ∃ v : E,
      Real.sqrt (chartMetricInner (I := I) g q
          (extChartAt I q q) v v) = ℓ * (t₁ - t₀) ∧
      ∀ r ∈ Icc t₀ t₁, γ r
        = expMap (I := I) g q
            ((((r - t₀) / (t₁ - t₀)) • v : E) : TangentSpace I q) := by
  classical
  subst hq
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M' := hg
  set q : M' := γ t₀ with hqdef
  obtain ⟨ρeq, hρeq, hdomeq, hsrceq, hinjeq, hkey⟩ :=
    exists_gauss_equality_geodesic (I := I) g q
  obtain ⟨εed, δed, hεed, hδed, hdomed, hsrced, hinjed, hopened, hformula,
    houtside⟩ := exists_edist_expMap_ball (I := I) g hg q
  obtain ⟨εg, cg, hεg, hcg, hdomg, hsrcg, hinjg, hopeng, hkeyg⟩ :=
    exists_le_pathELength (I := I) g q
  obtain ⟨-, -, -, hGram⟩ := hkeyg
  -- the length threshold for `t₁ - t₀`
  set η : ℝ := min (δed / ℓ) (ρeq / ((Real.sqrt cg + 1) * ℓ)) with hηdef
  have hη : 0 < η := by
    have h1 : 0 < δed / ℓ := by positivity
    have h2 : 0 < ρeq / ((Real.sqrt cg + 1) * ℓ) := by
      have : 0 < Real.sqrt cg + 1 := by positivity
      positivity
    exact lt_min h1 h2
  set t₁ : ℝ := min B (t₀ + η / 2) with ht₁def
  have ht₀t₁ : t₀ < t₁ := lt_min ht₀B (by linarith)
  have ht₁B : t₁ ≤ B := min_le_left _ _
  have hΔη : t₁ - t₀ < η := by
    have : t₁ ≤ t₀ + η / 2 := min_le_right _ _
    linarith
  set Δ : ℝ := t₁ - t₀ with hΔdef
  have hΔ : 0 < Δ := by simp only [hΔdef]; linarith
  have ht₁mem : t₁ ∈ Icc t₀ B := ⟨ht₀t₁.le, ht₁B⟩
  -- `γ t₁` lies in the metric normal ball at `q`
  have hlt_δ : ℓ * Δ < δed := by
    have hηδ : η ≤ δed / ℓ := min_le_left _ _
    calc ℓ * Δ < ℓ * η := mul_lt_mul_of_pos_left hΔη hℓ
      _ ≤ ℓ * (δed / ℓ) := mul_le_mul_of_nonneg_left hηδ hℓ.le
      _ = δed := by field_simp
  have hmem : γ t₁ ∈ (fun w : E =>
      expMap (I := I) g q (w : TangentSpace I q)) '' ball (0 : E) εed := by
    by_contra hout
    have h1 := houtside _ hout
    rw [hedist t₁ ht₁mem] at h1
    have h2 : δed ≤ ℓ * Δ := by
      have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
      linarith
    linarith
  obtain ⟨v, hv_ball, hv_eq'⟩ := hmem
  rw [mem_ball_zero_iff] at hv_ball
  have hv_eq : expMap (I := I) g q (v : TangentSpace I q) = γ t₁ := hv_eq'
  -- the radial length of `v` is the length of the subsegment
  have hQv_nonneg : 0 ≤ chartMetricInner (I := I) g q (extChartAt I q q) v v :=
    chartMetricInner_self_nonneg_of_mem_target (I := I) g q
      (mem_extChartAt_target q) v
  have hlen : Real.sqrt (chartMetricInner (I := I) g q
      (extChartAt I q q) v v) = ℓ * Δ := by
    have h1 := hformula v hv_ball
    rw [hv_eq, hedist t₁ ht₁mem] at h1
    have h2 : ℓ * (t₁ - t₀) = Real.sqrt (chartMetricInner (I := I) g q
        (extChartAt I q q) v v) :=
      (ENNReal.ofReal_eq_ofReal_iff
        (mul_nonneg hℓ.le (by linarith [ht₀t₁])) (Real.sqrt_nonneg _)).mp h1
    rw [hΔdef]
    exact h2.symm
  -- `v` is inside the Gauss radius of the equality machinery
  have hvρ : ‖v‖ < ρeq := by
    have hQv : chartMetricInner (I := I) g q (extChartAt I q q) v v
        = (ℓ * Δ) ^ 2 := by
      have h := congrArg (fun x : ℝ => x ^ 2) hlen
      simp only [] at h
      rwa [Real.sq_sqrt hQv_nonneg] at h
    have h1 : ‖v‖ ^ 2 ≤ cg * (ℓ * Δ) ^ 2 := by
      have := hGram v
      rwa [hQv] at this
    have h2 : ‖v‖ ≤ Real.sqrt cg * (ℓ * Δ) := by
      have hb : (0 : ℝ) ≤ Real.sqrt cg * (ℓ * Δ) := by positivity
      have hsq : ‖v‖ ^ 2 ≤ (Real.sqrt cg * (ℓ * Δ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hcg.le]
        exact h1
      have hroot := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (norm_nonneg v), Real.sqrt_sq hb] at hroot
    have h3 : Real.sqrt cg * (ℓ * Δ) < ρeq := by
      have hηρ : η ≤ ρeq / ((Real.sqrt cg + 1) * ℓ) := min_le_right _ _
      have hpos : 0 < (Real.sqrt cg + 1) * ℓ := by positivity
      have h4 : Δ < ρeq / ((Real.sqrt cg + 1) * ℓ) := lt_of_lt_of_le hΔη hηρ
      have h5 : (Real.sqrt cg + 1) * ℓ * Δ < ρeq := by
        calc (Real.sqrt cg + 1) * ℓ * Δ
            < (Real.sqrt cg + 1) * ℓ * (ρeq / ((Real.sqrt cg + 1) * ℓ)) :=
              mul_lt_mul_of_pos_left h4 hpos
          _ = ρeq := by field_simp
      have h6 : Real.sqrt cg * (ℓ * Δ) ≤ (Real.sqrt cg + 1) * ℓ * Δ := by
        nlinarith [Real.sqrt_nonneg cg, mul_pos hℓ hΔ]
      linarith
    linarith
  -- the reparametrized subsegment
  set σ : ℝ → M' := fun s => γ (t₀ + s * Δ) with hσdef
  have hmaps : ∀ s ∈ Icc (0 : ℝ) 1, t₀ + s * Δ ∈ Icc t₀ t₁ := by
    intro s hs
    constructor
    · nlinarith [hs.1, hs.2]
    · have : t₀ + s * Δ ≤ t₀ + 1 * Δ := by nlinarith [hs.1, hs.2]
      simpa [hΔdef] using this
  have haffine : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun s : ℝ => t₀ + s * Δ) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hσC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) := by
    refine ContMDiffOn.comp (t := Icc t₀ B) hγ haffine.contMDiffOn ?_
    intro s hs
    exact Icc_subset_Icc le_rfl ht₁B (hmaps s hs)
  have hσ0 : σ 0 = q := by
    simp only [hσdef, hqdef]
    norm_num
  have hσ1 : σ 1 = expMap (I := I) g q (v : TangentSpace I q) := by
    simp only [hσdef]
    rw [show t₀ + 1 * Δ = t₁ by rw [hΔdef]; ring]
    exact hv_eq.symm
  -- the running-length identity for `σ`
  have hrun : ∀ s ∈ Icc (0 : ℝ) 1, Manifold.pathELength I σ 0 s
      = ENNReal.ofReal (s * Real.sqrt (chartMetricInner (I := I) g q
          (extChartAt I q q) v v)) := by
    intro s hs
    rw [hlen]
    have hcomp : Manifold.pathELength I (γ ∘ fun s : ℝ => t₀ + s * Δ) 0 s
        = Manifold.pathELength I γ (t₀ + 0 * Δ) (t₀ + s * Δ) := by
      refine Manifold.pathELength_comp_of_monotoneOn hs.1 ?_ ?_ ?_
      · intro x _ y _ hxy
        nlinarith
      · fun_prop
      · refine (hγ.mono ?_).mdifferentiableOn one_ne_zero
        refine Icc_subset_Icc ?_ ?_
        · nlinarith [hs.1]
        · have := (hmaps s hs).2
          exact this.trans ht₁B
    have hσγ : Manifold.pathELength I σ 0 s
        = Manifold.pathELength I (γ ∘ fun s : ℝ => t₀ + s * Δ) 0 s := rfl
    rw [hσγ, hcomp]
    rw [show t₀ + 0 * Δ = t₀ by ring]
    rw [harc (t₀ + s * Δ) (Icc_subset_Icc le_rfl ht₁B (hmaps s hs))]
    congr 1
    ring
  -- the equality case: `σ` is the radial geodesic
  have hout := hkey v hvρ σ hσC1 hσ0 hσ1 hrun
  refine ⟨t₁, ht₀t₁, ht₁B, v, ?_, ?_⟩
  · simpa [hΔdef] using hlen
  · intro r hr
    have hs : (r - t₀) / Δ ∈ Icc (0 : ℝ) 1 := by
      constructor
      · have : 0 ≤ r - t₀ := by linarith [hr.1]
        positivity
      · rw [div_le_one hΔ]
        have := hr.2
        simp only [hΔdef]
        linarith
    have h1 := hout.1 _ hs
    have h2 : σ ((r - t₀) / Δ) = γ r := by
      simp only [hσdef]
      congr 1
      rw [div_mul_cancel₀ _ hΔ.ne']
      ring
    rw [h2] at h1
    rw [hΔdef] at h1
    exact h1

/-- **Math.** **The two-sided corner argument** (do Carmo Ch. 3, Cor. 3.9, the
localization at one interior time). Let `γ` be arclength-proportional and
distance-realizing on `[A, B]` with speed `ℓ > 0`, and `C¹` separately on
`[A, u]` and `[u, B]` for an interior time `u`.  Anchoring the radial
identification (`exists_radial_of_anchored`) at `q = γ u` along the forward
subsegment and along the time-reversed backward subsegment exhibits `γ` near
`u` as a broken pair of radial geodesics `exp_q (· • v₁)`, `exp_q (· • v₂)`;
since the pair realizes the distance `2η` between `exp_q (η • u₁)` and
`exp_q (η • u₂)` for every small `η`, corner rigidity
(`eq_neg_of_forall_edist_expMap_eq`) gives `u₂ = -u₁`: near `u` the curve is a
single exponential ray, hence satisfies the geodesic equation at `u`
(`exists_isGeodesicOn_expMap_ray` + locality of the geodesic equation). -/
theorem hasGeodesicEquationAt_of_arclength_edist (g : RiemannianMetric I M')
    (hg : g.IsRiemannianDist) {γ : ℝ → M'} {A B u ℓ : ℝ}
    (hAu : A < u) (huB : u < B) (hℓ : 0 < ℓ)
    (hγL : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc A u))
    (hγR : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc u B))
    (harc : letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      ∀ s t : ℝ, A ≤ s → s ≤ t → t ≤ B →
        Manifold.pathELength I γ s t = ENNReal.ofReal (ℓ * (t - s)))
    (hedist : ∀ s t : ℝ, A ≤ s → s ≤ t → t ≤ B →
      edist (γ s) (γ t) = ENNReal.ofReal (ℓ * (t - s))) :
    HasGeodesicEquationAt (I := I) g γ u := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M' := hg
  set q : M' := γ u with hqdef
  -- the forward radial identification on `[u, t₁]`
  obtain ⟨t₁, hut₁, ht₁B, v₂, hlen₂, hrep₂⟩ :=
    exists_radial_of_anchored (I := I) g hg (t₀ := u) (B := B) rfl huB hℓ hγR
      (fun t ht => harc u t hAu.le ht.1 ht.2)
      (fun t ht => hedist u t hAu.le ht.1 ht.2)
  -- the time-reversed curve, and its radial identification on `[u, s₁]`
  set γrev : ℝ → M' := fun s => γ (2 * u - s) with hγrevdef
  have hγrevu : γrev u = q := by
    simp only [hγrevdef, hqdef]
    congr 1
    ring
  have haffrev : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun s : ℝ => 2 * u - s) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hγrevC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γrev (Icc u (2 * u - A)) := by
    refine ContMDiffOn.comp (t := Icc A u) hγL haffrev.contMDiffOn ?_
    intro s hs
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hγrevarc : ∀ t ∈ Icc u (2 * u - A), Manifold.pathELength I γrev u t
      = ENNReal.ofReal (ℓ * (t - u)) := by
    intro t ht
    have hcomp : Manifold.pathELength I (γ ∘ fun s : ℝ => 2 * u - s) u t
        = Manifold.pathELength I γ (2 * u - t) (2 * u - u) := by
      refine Manifold.pathELength_comp_of_antitoneOn ht.1 ?_ ?_ ?_
      · intro x _ y _ hxy
        dsimp only
        linarith
      · fun_prop
      · refine (hγL.mono ?_).mdifferentiableOn one_ne_zero
        refine Icc_subset_Icc ?_ ?_
        · linarith [ht.2]
        · linarith
    have hLHS : Manifold.pathELength I γrev u t
        = Manifold.pathELength I γ (2 * u - t) (2 * u - u) := hcomp
    rw [hLHS, show (2 * u - u : ℝ) = u by ring,
      harc (2 * u - t) u (by linarith [ht.2]) (by linarith [ht.1]) huB.le]
    congr 1
    ring
  have hγrevedist : ∀ t ∈ Icc u (2 * u - A), edist (γrev u) (γrev t)
      = ENNReal.ofReal (ℓ * (t - u)) := by
    intro t ht
    have h2 : γrev t = γ (2 * u - t) := rfl
    rw [hγrevu, hqdef, h2, edist_comm,
      hedist (2 * u - t) u (by linarith [ht.2]) (by linarith [ht.1]) huB.le]
    congr 1
    ring
  obtain ⟨s₁, hus₁, hs₁A, v₁, hlen₁, hrep₁⟩ :=
    exists_radial_of_anchored (I := I) g hg (t₀ := u) (B := 2 * u - A)
      hγrevu (by linarith) hℓ hγrevC1 hγrevarc hγrevedist
  -- normalized velocities of the two legs
  set L₁ : ℝ := ℓ * (s₁ - u) with hL₁def
  set L₂ : ℝ := ℓ * (t₁ - u) with hL₂def
  have hL₁ : 0 < L₁ := by
    rw [hL₁def]
    have : 0 < s₁ - u := by linarith
    positivity
  have hL₂ : 0 < L₂ := by
    rw [hL₂def]
    have : 0 < t₁ - u := by linarith
    positivity
  set w₁ : E := L₁⁻¹ • v₁ with hw₁def
  set w₂ : E := L₂⁻¹ • v₂ with hw₂def
  have hQ₁ : chartMetricInner (I := I) g q (extChartAt I q q) v₁ v₁
      = L₁ ^ 2 := by
    have hnn : 0 ≤ chartMetricInner (I := I) g q (extChartAt I q q) v₁ v₁ :=
      chartMetricInner_self_nonneg_of_mem_target (I := I) g q
        (mem_extChartAt_target q) v₁
    have h := congrArg (fun x : ℝ => x ^ 2) hlen₁
    simp only [] at h
    rw [Real.sq_sqrt hnn] at h
    rw [h, hL₁def]
  have hQ₂ : chartMetricInner (I := I) g q (extChartAt I q q) v₂ v₂
      = L₂ ^ 2 := by
    have hnn : 0 ≤ chartMetricInner (I := I) g q (extChartAt I q q) v₂ v₂ :=
      chartMetricInner_self_nonneg_of_mem_target (I := I) g q
        (mem_extChartAt_target q) v₂
    have h := congrArg (fun x : ℝ => x ^ 2) hlen₂
    simp only [] at h
    rw [Real.sq_sqrt hnn] at h
    rw [h, hL₂def]
  have hunit₁ : chartMetricInner (I := I) g q (extChartAt I q q) w₁ w₁ = 1 := by
    rw [hw₁def, chartMetricInner_smul_left, chartMetricInner_smul_right, hQ₁]
    field_simp
  have hunit₂ : chartMetricInner (I := I) g q (extChartAt I q q) w₂ w₂ = 1 := by
    rw [hw₂def, chartMetricInner_smul_left, chartMetricInner_smul_right, hQ₂]
    field_simp
  -- the broken pair realizes the distance `2η`, for every small `η`
  have hcorner : ∀ η : ℝ, 0 < η → η < min L₁ L₂ →
      edist (expMap (I := I) g q ((η • w₁ : E) : TangentSpace I q))
        (expMap (I := I) g q ((η • w₂ : E) : TangentSpace I q))
      = ENNReal.ofReal (2 * η) := by
    intro η hη hηlt
    have hηL₁ : η < L₁ := lt_of_lt_of_le hηlt (min_le_left _ _)
    have hηL₂ : η < L₂ := lt_of_lt_of_le hηlt (min_le_right _ _)
    have hηℓ : 0 < η / ℓ := by positivity
    -- the backward point
    have hb : expMap (I := I) g q ((η • w₁ : E) : TangentSpace I q)
        = γ (u - η / ℓ) := by
      have hmem : u + η / ℓ ∈ Icc u s₁ := by
        constructor
        · linarith
        · have : η / ℓ < s₁ - u := by
            rw [div_lt_iff₀ hℓ]
            calc η < L₁ := hηL₁
              _ = (s₁ - u) * ℓ := by rw [hL₁def]; ring
          linarith
      have h1 := hrep₁ _ hmem
      have h2 : γrev (u + η / ℓ) = γ (u - η / ℓ) := by
        simp only [hγrevdef]
        congr 1
        ring
      have h3 : (((u + η / ℓ - u) / (s₁ - u)) • v₁ : E) = (η • w₁ : E) := by
        rw [hw₁def, smul_smul, hL₁def]
        congr 1
        field_simp
        ring
      rw [h2, h3] at h1
      exact h1.symm
    -- the forward point
    have hf : expMap (I := I) g q ((η • w₂ : E) : TangentSpace I q)
        = γ (u + η / ℓ) := by
      have hmem : u + η / ℓ ∈ Icc u t₁ := by
        constructor
        · linarith
        · have : η / ℓ < t₁ - u := by
            rw [div_lt_iff₀ hℓ]
            calc η < L₂ := hηL₂
              _ = (t₁ - u) * ℓ := by rw [hL₂def]; ring
          linarith
      have h1 := hrep₂ _ hmem
      have h3 : (((u + η / ℓ - u) / (t₁ - u)) • v₂ : E) = (η • w₂ : E) := by
        rw [hw₂def, smul_smul, hL₂def]
        congr 1
        field_simp
        ring
      rw [h3] at h1
      exact h1.symm
    rw [hb, hf]
    have hbound₁ : A ≤ u - η / ℓ := by
      have h1 : η / ℓ ≤ s₁ - u := by
        rw [div_le_iff₀ hℓ]
        calc η ≤ L₁ := hηL₁.le
          _ = (s₁ - u) * ℓ := by rw [hL₁def]; ring
      have h2 : s₁ ≤ 2 * u - A := hs₁A
      linarith
    have hbound₂ : u + η / ℓ ≤ B := by
      have h1 : η / ℓ ≤ t₁ - u := by
        rw [div_le_iff₀ hℓ]
        calc η ≤ L₂ := hηL₂.le
          _ = (t₁ - u) * ℓ := by rw [hL₂def]; ring
      linarith
    rw [hedist (u - η / ℓ) (u + η / ℓ) hbound₁ (by linarith) hbound₂]
    congr 1
    field_simp
    ring
  -- corner rigidity: the two legs are anti-parallel
  have hneg : w₂ = -w₁ :=
    eq_neg_of_forall_edist_expMap_eq (I := I) g hg q hunit₁ hunit₂
      (lt_min hL₁ hL₂) hcorner
  -- the single radial representation of `γ` around `u`
  have hrad : ∀ r ∈ Icc (2 * u - s₁) t₁,
      γ r = expMap (I := I) g q (((ℓ * (r - u)) • w₂ : E) : TangentSpace I q) := by
    intro r hr
    rcases le_total u r with h | h
    · -- forward leg
      have h1 := hrep₂ r ⟨h, hr.2⟩
      have h3 : (((r - u) / (t₁ - u)) • v₂ : E) = ((ℓ * (r - u)) • w₂ : E) := by
        rw [hw₂def, smul_smul, hL₂def]
        congr 1
        have ht₁u : t₁ - u ≠ 0 := sub_ne_zero.mpr hut₁.ne'
        field_simp
      rw [h3] at h1
      exact h1
    · -- backward leg
      have hmem : 2 * u - r ∈ Icc u s₁ := by
        constructor
        · linarith
        · linarith [hr.1]
      have h1 := hrep₁ _ hmem
      have h2 : γrev (2 * u - r) = γ r := by
        simp only [hγrevdef]
        congr 1
        ring
      have h3 : (((2 * u - r - u) / (s₁ - u)) • v₁ : E)
          = ((ℓ * (r - u)) • w₂ : E) := by
        rw [hneg, hw₁def, smul_neg, smul_smul, ← neg_smul, hL₁def]
        congr 1
        have hs₁u : s₁ - u ≠ 0 := sub_ne_zero.mpr hus₁.ne'
        field_simp
        ring
      rw [h2, h3] at h1
      exact h1
  -- the exponential ray through `q` is a geodesic around time `0`
  obtain ⟨ρray, bray, hρray, hbray, hdomray, hraykey⟩ :=
    exists_isGeodesicOn_expMap_ray (I := I) g q
  set c₀ : ℝ := ρray / (2 * (‖w₂‖ + 1)) with hc₀def
  have hc₀ : 0 < c₀ := by
    rw [hc₀def]
    positivity
  set z : E := c₀ • w₂ with hzdef
  have hz : ‖z‖ < ρray := by
    rw [hzdef, norm_smul, Real.norm_of_nonneg hc₀.le, hc₀def,
      div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w₂]
  obtain ⟨-, -, -, hraygeo⟩ := hraykey z hz
  have haff := isGeodesicOn_comp_affine (κ := ℓ / c₀) (c := -(ℓ * u) / c₀)
    hraygeo
  have hfun : (fun r : ℝ => expMap (I := I) g q
        (((ℓ / c₀ * r + -(ℓ * u) / c₀) • z : E) : TangentSpace I q))
      = fun r : ℝ => expMap (I := I) g q
        (((ℓ * (r - u)) • w₂ : E) : TangentSpace I q) := by
    funext r
    congr 1
    rw [hzdef, smul_smul]
    congr 1
    field_simp
    ring
  have humem : u ∈ (fun r : ℝ => ℓ / c₀ * r + -(ℓ * u) / c₀) ⁻¹'
      (Ioo (-bray) bray) := by
    have hval : ℓ / c₀ * u + -(ℓ * u) / c₀ = 0 := by
      field_simp
      ring
    simp only [mem_preimage, hval, mem_Ioo]
    constructor <;> linarith
  have hP : HasGeodesicEquationAt (I := I) g
      (fun r : ℝ => expMap (I := I) g q
        (((ℓ * (r - u)) • w₂ : E) : TangentSpace I q)) u := by
    have h1 := haff u humem
    rwa [hfun] at h1
  have hev : γ =ᶠ[𝓝 u] fun r : ℝ => expMap (I := I) g q
      (((ℓ * (r - u)) • w₂ : E) : TangentSpace I q) := by
    have hoo : Ioo (2 * u - s₁) t₁ ∈ 𝓝 u :=
      Ioo_mem_nhds (by linarith) hut₁
    filter_upwards [hoo] with r hr
    exact hrad r ⟨hr.1.le, hr.2.le⟩
  exact hasGeodesicEquationAt_congr_of_eventuallyEq hev hP

/-- **Math.** **Minimizing curves are geodesics, `C¹` case** (do Carmo Ch. 3,
Corollary 3.9, moving centers). Let `γ : [a, b] → M` be a `C¹` curve
parametrized proportionally to arc length (`ℓ(γ|[a,t]) = ℓ · (t - a)`) which
realizes the metric distance between its endpoints
(`d(γ a, γ b) = ℓ · (b - a)`; under `g.IsRiemannianDist` the distance is the
infimum of competitor lengths, so this is do Carmo's "`ℓ(γ) ≤` the length of
any other curve joining `γ a` to `γ b`"). Then `γ` satisfies the intrinsic
geodesic equation at every interior time. -/
theorem isGeodesicOn_of_arclength_edist (g : RiemannianMetric I M')
    (hg : g.IsRiemannianDist) {γ : ℝ → M'} {a b ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (harc : letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      ∀ t ∈ Icc a b, Manifold.pathELength I γ a t = ENNReal.ofReal (ℓ * (t - a)))
    (hmin : edist (γ a) (γ b) = ENNReal.ofReal (ℓ * (b - a))) :
    IsGeodesicOn (I := I) g γ (Ioo a b) := by
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M' := hg
  intro u hu
  have hupper : ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
      edist (γ s) (γ t) ≤ Manifold.pathELength I γ s t := fun s t has hst htb =>
    OpenGA.HopfRinow.edist_le_pathELength_of_cmdiff
      (hγ.mono (Icc_subset_Icc has htb)) hst
  have hedist : ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
      edist (γ s) (γ t) = ENNReal.ofReal (ℓ * (t - s)) := fun s t has hst htb =>
    edist_segment_of_arclength (I := I) g hℓ hupper harc hmin has hst htb
  rcases hℓ.eq_or_lt with hℓ0 | hℓpos
  · -- speed zero: the curve is constant near `u`, and constants are geodesics
    have hconst : ∀ t ∈ Icc a b, γ t = γ a := by
      intro t ht
      have h1 := hedist a t le_rfl ht.1 ht.2
      rw [← hℓ0] at h1
      simp only [zero_mul, ENNReal.ofReal_zero] at h1
      exact (edist_eq_zero.mp h1).symm
    have hcgeo : HasGeodesicEquationAt (I := I) g (fun _ : ℝ => γ a) u :=
      isGeodesic_const (I := I) g (γ a) u
    refine hasGeodesicEquationAt_congr_of_eventuallyEq ?_ hcgeo
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with r hr
    exact hconst r ⟨hr.1.le, hr.2.le⟩
  · exact hasGeodesicEquationAt_of_arclength_edist (I := I) g hg hu.1 hu.2
      hℓpos (hγ.mono (Icc_subset_Icc le_rfl hu.2.le))
      (hγ.mono (Icc_subset_Icc hu.1.le le_rfl))
      (fun s t has hst htb =>
        pathELength_segment_of_arclength (I := I) g hℓ harc has hst htb)
      hedist

/-- **Math.** **Minimizing curves are geodesics, piecewise-`C¹` case**
(do Carmo Ch. 3, Corollary 3.9, in do Carmo's regularity class). Let `γ` be
piecewise `C¹` with respect to the partition `τ 0 ≤ ⋯ ≤ τ n`, parametrized
proportionally to arc length, and realizing the metric distance between its
endpoints. Then `γ` satisfies the intrinsic geodesic equation at every
interior time — including the partition vertices: a minimizing broken
geodesic has no corner. -/
theorem isGeodesicOn_piecewise_of_arclength_edist (g : RiemannianMetric I M')
    (hg : g.IsRiemannianDist) {γ : ℝ → M'} {n : ℕ} {τ : ℕ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hτ : ∀ i < n, τ i ≤ τ (i + 1))
    (hγ : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc (τ i) (τ (i + 1))))
    (harc : letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      ∀ t ∈ Icc (τ 0) (τ n), Manifold.pathELength I γ (τ 0) t
        = ENNReal.ofReal (ℓ * (t - τ 0)))
    (hmin : edist (γ (τ 0)) (γ (τ n)) = ENNReal.ofReal (ℓ * (τ n - τ 0))) :
    IsGeodesicOn (I := I) g γ (Ioo (τ 0) (τ n)) := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M' := hg
  intro u hu
  have hupper : ∀ s t : ℝ, τ 0 ≤ s → s ≤ t → t ≤ τ n →
      edist (γ s) (γ t) ≤ Manifold.pathELength I γ s t := fun s t hs hst ht =>
    edist_le_pathELength_piecewise_partition (I := I) g hg hτ hγ hs hst ht
  have hedist : ∀ s t : ℝ, τ 0 ≤ s → s ≤ t → t ≤ τ n →
      edist (γ s) (γ t) = ENNReal.ofReal (ℓ * (t - s)) := fun s t hs hst ht =>
    edist_segment_of_arclength (I := I) g hℓ hupper harc hmin hs hst ht
  rcases hℓ.eq_or_lt with hℓ0 | hℓpos
  · -- speed zero: constant curve
    have hconst : ∀ t ∈ Icc (τ 0) (τ n), γ t = γ (τ 0) := by
      intro t ht
      have h1 := hedist (τ 0) t le_rfl ht.1 ht.2
      rw [← hℓ0] at h1
      simp only [zero_mul, ENNReal.ofReal_zero] at h1
      exact (edist_eq_zero.mp h1).symm
    have hcgeo : HasGeodesicEquationAt (I := I) g (fun _ : ℝ => γ (τ 0)) u :=
      isGeodesic_const (I := I) g (γ (τ 0)) u
    refine hasGeodesicEquationAt_congr_of_eventuallyEq ?_ hcgeo
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with r hr
    exact hconst r ⟨hr.1.le, hr.2.le⟩
  -- positive speed: find the pieces adjacent to `u`
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0] at hu
      exact absurd (hu.1.trans hu.2) (lt_irrefl _)
    · exact h0
  -- the backward piece: the largest `k` with `τ k < u`
  set k : ℕ := Nat.findGreatest (fun i => τ i < u) n with hkdef
  have hk_prop : τ k < u := by
    have h0 : (fun i => τ i < u) 0 := hu.1
    exact Nat.findGreatest_spec (P := fun i => τ i < u) (Nat.zero_le n) h0
  have hk_le : k ≤ n := Nat.findGreatest_le n
  have hk_lt : k < n := by
    rcases lt_or_eq_of_le hk_le with h | h
    · exact h
    · exfalso
      rw [h] at hk_prop
      exact absurd (hk_prop.trans hu.2) (lt_irrefl _)
  have hk_max : u ≤ τ (k + 1) := by
    by_contra hcon
    push_neg at hcon
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self k) hk_lt hcon
  -- the forward piece: the largest `j` with `τ j ≤ u`
  set j : ℕ := Nat.findGreatest (fun i => τ i ≤ u) n with hjdef
  have hj_prop : τ j ≤ u := by
    have h0 : (fun i => τ i ≤ u) 0 := hu.1.le
    exact Nat.findGreatest_spec (P := fun i => τ i ≤ u) (Nat.zero_le n) h0
  have hj_le : j ≤ n := Nat.findGreatest_le n
  have hj_lt : j < n := by
    rcases lt_or_eq_of_le hj_le with h | h
    · exact h
    · exfalso
      rw [h] at hj_prop
      exact absurd (lt_of_le_of_lt hj_prop hu.2) (lt_irrefl _)
  have hj_max : u < τ (j + 1) := by
    by_contra hcon
    push_neg at hcon
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self j) hj_lt hcon
  -- the two-sided argument on `[τ k, τ (j + 1)]`
  have hA0 : τ 0 ≤ τ k := partition_le hτ (Nat.zero_le k) hk_le
  have hBn : τ (j + 1) ≤ τ n := partition_le hτ (Nat.succ_le_of_lt hj_lt) le_rfl
  refine hasGeodesicEquationAt_of_arclength_edist (I := I) g hg hk_prop hj_max
    hℓpos ((hγ k hk_lt).mono (Icc_subset_Icc le_rfl hk_max))
    ((hγ j hj_lt).mono (Icc_subset_Icc hj_prop le_rfl))
    (fun s t hs hst ht =>
      pathELength_segment_of_arclength (I := I) g hℓ harc (hA0.trans hs) hst
        (ht.trans hBn))
    (fun s t hs hst ht => hedist s t (hA0.trans hs) hst (ht.trans hBn))

/-- **Math.** **Minimizing curves are geodesics, in do Carmo's literal
hypothesis form** (do Carmo Ch. 3, Corollary 3.9). If a piecewise-`C¹` curve
`γ`, parametrized proportionally to arc length, has length not exceeding that
of any (`C¹`, hence a fortiori any piecewise-`C¹`) curve joining `γ (τ 0)` to
`γ (τ n)`, then `γ` satisfies the intrinsic geodesic equation at every
interior time.  Under `g.IsRiemannianDist` the competitor bound identifies
`ℓ(γ)` with the Riemannian distance (`edist` is the infimum of competitor
lengths, `exists_lt_of_riemannianEDist_lt`), reducing to
`isGeodesicOn_piecewise_of_arclength_edist`. -/
theorem isGeodesicOn_piecewise_of_arclength_forall_le (g : RiemannianMetric I M')
    (hg : g.IsRiemannianDist) {γ : ℝ → M'} {n : ℕ} {τ : ℕ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hτ : ∀ i < n, τ i ≤ τ (i + 1))
    (hγ : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc (τ i) (τ (i + 1))))
    (harc : letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      ∀ t ∈ Icc (τ 0) (τ n), Manifold.pathELength I γ (τ 0) t
        = ENNReal.ofReal (ℓ * (t - τ 0)))
    (hmin : letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      ∀ σ : ℝ → M', ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) →
        σ 0 = γ (τ 0) → σ 1 = γ (τ n) →
        Manifold.pathELength I γ (τ 0) (τ n) ≤ Manifold.pathELength I σ 0 1) :
    IsGeodesicOn (I := I) g γ (Ioo (τ 0) (τ n)) := by
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M' := hg
  have hτ0n : τ 0 ≤ τ n := partition_le hτ (Nat.zero_le n) le_rfl
  -- the competitor bound realizes the distance between the endpoints
  have hreal : edist (γ (τ 0)) (γ (τ n))
      = Manifold.pathELength I γ (τ 0) (τ n) := by
    refine le_antisymm
      (edist_le_pathELength_piecewise_partition (I := I) g hg hτ hγ le_rfl
        hτ0n le_rfl) ?_
    by_contra hcon
    push_neg at hcon
    rw [IsRiemannianManifold.out (I := I) (γ (τ 0)) (γ (τ n))] at hcon
    obtain ⟨σ, hσ0, hσ1, hσC1, hσlt⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hcon
    exact absurd (hmin σ hσC1 hσ0 hσ1) (not_le.mpr hσlt)
  have hmin' : edist (γ (τ 0)) (γ (τ n))
      = ENNReal.ofReal (ℓ * (τ n - τ 0)) := by
    rw [hreal, harc (τ n) ⟨hτ0n, le_rfl⟩]
  exact isGeodesicOn_piecewise_of_arclength_edist (I := I) g hg hℓ hτ hγ harc
    hmin'

end Exponential

end PetersenLib
