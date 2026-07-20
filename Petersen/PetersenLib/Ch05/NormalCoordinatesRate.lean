import PetersenLib.Ch05.NormalCoordinatesFlatness
import PetersenLib.Riemannian.Exponential.TotallyNormalCInfty

/-!
# Petersen Ch. 5, §5.5 — Lemma 5.5.7: the `O(r²)` rate
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

open PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] [T2Space M]

set_option maxHeartbeats 1000000 in
/-- **Math.** The chart reading of `exp_p` is `C^∞` on a ball around the origin. -/
theorem Exponential.exists_contDiffOn_infty_extChartAt_expMap_ball
    (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      ContDiffOn ℝ ∞
        (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
        (ball (0 : E) ρ) := by
  classical
  obtain ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, hGpair, hslice⟩ :=
    Exponential.exists_pairMap_contDiffOn_infty (I := I) g p
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  have hTIoo : T ∈ Ioo (-ε) ε := ⟨lt_trans (neg_lt_zero.mpr hε) hT, hTε⟩
  set ρ : ℝ := T * r with hρdef
  have hρpos : 0 < ρ := by positivity
  have key : ∀ w : E, ‖w‖ < ρ →
      ((w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))
        = (Z ((extChartAt I p p, T⁻¹ • w) : E × E) T).1) := by
    intro w hw
    set u : E := T⁻¹ • w with hudef
    have hu : ‖u‖ < r := by
      rw [hudef, norm_smul, norm_inv, Real.norm_of_nonneg hT.le]
      rw [inv_mul_lt_iff₀ hT]
      rw [hρdef] at hw
      linarith [hw]
    have hTu : (T : ℝ) • u = w := smul_inv_smul₀ hT.ne' w
    have hzu : ((extChartAt I p p, u) : E × E) ∈ closedBall z₀ r := by
      rw [mem_closedBall, hz₀def, Prod.dist_eq]
      simp only [dist_self, dist_zero_right]
      exact max_le hr.le hu.le
    obtain ⟨h0u, hdu, hmemu⟩ := hflow _ hzu
    have hdIoo : ∀ s ∈ Ioo (-ε) ε,
        HasDerivAt (Z ((extChartAt I p p, u) : E × E))
          (geodesicSprayCoord (I := I) g p
            (Z ((extChartAt I p p, u) : E × E) s).1
            (Z ((extChartAt I p p, u) : E × E) s).2) s := fun s hs =>
      (hdu s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have hmemΨ : ∀ s ∈ Ioo (-ε) ε,
        Z ((extChartAt I p p, u) : E × E) s ∈
          (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target := by
      intro s hs
      rw [extChartAt_tangent_target (I := I) p]
      exact hmemu s (Ioo_subset_Icc_self hs)
    obtain ⟨hwit, hsrc, hchart⟩ :=
      isGeodesicOnWithInitial_of_hasDerivAt_sprayCoord (I := I) g p
        (u : TangentSpace I p) h0u hdIoo hmemΨ
    have hTu' : (T • (u : TangentSpace I p)) = (w : TangentSpace I p) := by
      show (T • u : E) = w
      exact hTu
    have hwitW : IsGeodesicOnWithInitial (I := I) g
        (fun t => (((extChartAt I.tangent
          (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
            (Z ((extChartAt I p p, u) : E × E) (T * t))).proj))
        {t : ℝ | T * t ∈ Ioo (-ε) ε} p (w : TangentSpace I p) := by
      obtain ⟨fW, hproj, hf0, hint⟩ := hwit.fiberScale T
      refine ⟨fW, hproj, ?_, hint⟩
      rw [hf0]
      exact congrArg
        (fun v : TangentSpace I p => (⟨p, v⟩ : TangentBundle I M)) hTu'
    have hJ'o : IsOpen {t : ℝ | T * t ∈ Ioo (-ε) ε} :=
      isOpen_Ioo.preimage (continuous_const.mul continuous_id)
    have hJ'c : IsPreconnected {t : ℝ | T * t ∈ Ioo (-ε) ε} := by
      have hJ'eq : {t : ℝ | T * t ∈ Ioo (-ε) ε} = Ioo (-(ε / T)) (ε / T) := by
        ext t
        simp only [mem_setOf_eq, mem_Ioo]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨?_, ?_⟩
          · rw [← neg_div, div_lt_iff₀ hT]
            nlinarith
          · rw [lt_div_iff₀ hT]
            nlinarith
        · rintro ⟨h1, h2⟩
          rw [← neg_div, div_lt_iff₀ hT] at h1
          rw [lt_div_iff₀ hT] at h2
          exact ⟨by nlinarith, by nlinarith⟩
      rw [hJ'eq]; exact isPreconnected_Ioo
    have h0J' : (0 : ℝ) ∈ {t : ℝ | T * t ∈ Ioo (-ε) ε} := by
      simp only [mem_setOf_eq, mul_zero]
      exact ⟨neg_lt_zero.mpr hε, hε⟩
    have h1J' : (1 : ℝ) ∈ {t : ℝ | T * t ∈ Ioo (-ε) ε} := by
      simp only [mem_setOf_eq, mul_one]
      exact hTIoo
    have hsrcW : ∀ t ∈ {t : ℝ | T * t ∈ Ioo (-ε) ε},
        (((extChartAt I.tangent
          (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
            (Z ((extChartAt I p p, u) : E × E) (T * t))).proj) ∈
          (chartAt H p).source := fun t ht => hsrc (T * t) ht
    have hval := maximalGeodesic_eq_witness_of_mem_chart (I := I) hwitW
      hJ'o hJ'c h0J' hsrcW h1J'
    have hdom : (w : TangentSpace I p) ∈ expDomain (I := I) g p := by
      show (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p (w : TangentSpace I p)
      exact subset_maximalGeodesicInterval_of_witness (I := I) hwitW
        hJ'o hJ'c h0J' h1J'
    have hexp_eq : expMap (I := I) g p (w : TangentSpace I p)
        = (((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
            (Z ((extChartAt I p p, u) : E × E) (T * 1))).proj) := by
      show maximalGeodesic (I := I) g p (w : TangentSpace I p) 1 = _
      exact hval
    rw [mul_one] at hexp_eq
    refine ⟨hdom, ?_, ?_⟩
    · rw [hexp_eq]
      exact hsrc T hTIoo
    · rw [hexp_eq, hchart T hTIoo]
  refine ⟨ρ, hρpos, fun w hw => (key w hw).1, fun w hw => (key w hw).2.1, ?_⟩
  have hy : extChartAt I p p ∈ ball (extChartAt I p p) r := mem_ball_self hr
  exact (hslice _ hy).congr fun w hw => (key w (mem_ball_zero_iff.mp hw)).2.2

/-! ### The coordinate metric is `C²` on a ball -/

/-- **Math.** On a ball around the origin the coordinate metric `x ↦ g_ij(x) aⁱ bʲ` is
`C²`, uniformly in the vector slots: the radius depends only on `g` and `p`. -/
theorem exists_contDiffOn_two_expGram_ball (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ a b : E,
      ContDiffOn ℝ 2 (fun x : E => expGram (I := I) g p x a b) (ball (0 : E) ρ) := by
  classical
  obtain ⟨ρ, hρ, _hdom, hsrc, hCinf⟩ :=
    Exponential.exists_contDiffOn_infty_extChartAt_expMap_ball (I := I) g p
  refine ⟨ρ, hρ, fun a b x hx => ContDiffAt.contDiffWithinAt ?_⟩
  have hxb : ‖x‖ < ρ := by simpa using hx
  have htgt : expChart (I := I) g p x ∈ (extChartAt I p).target := by
    refine (extChartAt I p).map_source ?_
    rw [extChartAt_source]
    exact hsrc x hxb
  have hat : ContDiffAt ℝ ∞ (expChart (I := I) g p) x :=
    hCinf.contDiffAt (isOpen_ball.mem_nhds hx)
  have hat2 : ContDiffAt ℝ 2 (expChart (I := I) g p) x := hat.of_le (by norm_cast)
  have hDE : ContDiffAt ℝ 2 (fun y => fderiv ℝ (expChart (I := I) g p) y) x :=
    hat.fderiv_right (m := 2) (by norm_cast)
  have hGram : ∀ i j, ContDiffAt ℝ 2
      (fun y : E => chartGramOnE (I := I) g p i j (expChart (I := I) g p y)) x := by
    intro i j
    exact (((chartGramOnE_contDiffOn (I := I) g p i j).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds htgt)).of_le (by norm_cast)).comp x hat2
  have hcoord : ∀ (i : Fin (Module.finrank ℝ E)) (c : E), ContDiffAt ℝ 2
      (fun y : E => Geodesic.chartCoord (E := E) i (fderiv ℝ (expChart (I := I) g p) y c)) x := by
    intro i c
    have hev : ContDiffAt ℝ 2 (fun y : E => fderiv ℝ (expChart (I := I) g p) y c) x :=
      ((ContinuousLinearMap.apply ℝ E c).contDiff.contDiffAt).comp x hDE
    have := ((Geodesic.chartCoordFunctional (E := E) i).contDiff.contDiffAt).comp x hev
    simpa using this
  unfold expGram
  simp only [chartMetricInner_def]
  exact ContDiffAt.sum fun i _ =>
    ContDiffAt.sum fun j _ => ((hGram i j).mul (hcoord i a)).mul (hcoord j b)

/-! ### The `O(r²)` rate -/

/-- **Math.** Petersen Ch. 5, Lemma 5.5.7, in its slot-wise form: on a ball around the
origin of exponential coordinates whose radius depends only on `(g, p)`, each entry of
the coordinate metric differs from its value at `p` by `O(r²)`. -/
theorem exists_expGram_sub_le_sq (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ a b : E, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ ball (0 : E) ρ,
      |expGram (I := I) g p x a b - g.metricInner p a b| ≤ C * ‖x‖ ^ 2 := by
  classical
  obtain ⟨ρ, hρ, hC2⟩ := exists_contDiffOn_two_expGram_ball (I := I) g p
  refine ⟨ρ / 2, by linarith, fun a b => ?_⟩
  set F : E → ℝ := fun x : E => expGram (I := I) g p x a b with hFdef
  have hsub : closedBall (0 : E) (ρ / 2) ⊆ ball (0 : E) ρ := by
    intro y hy
    rw [mem_closedBall_zero_iff] at hy
    rw [mem_ball_zero_iff]
    linarith
  -- unpack `C²` into: `F` differentiable, `fderiv F` differentiable, `fderiv (fderiv F)` continuous
  have hFC : ContDiffOn ℝ 2 F (ball (0 : E) ρ) := hC2 a b
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball] at hFC
  obtain ⟨hFdiff, -, hDC⟩ := hFC
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
    contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball] at hDC
  obtain ⟨hDdiff, -, hDDC⟩ := hDC
  -- a uniform bound `K` on the second derivative over the compact half-ball
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : E) (ρ / 2)).exists_bound_of_continuousOn
    (hDDC.continuousOn.mono hsub)
  have hK0 : 0 ≤ K :=
    le_trans (norm_nonneg _) (hK 0 (mem_closedBall_self (by linarith)))
  -- the derivative vanishes at the origin (the jet), so the mean value theorem on the
  -- second derivative gives `‖dF_x‖ ≤ K‖x‖`
  have hD0 : fderiv ℝ F 0 = 0 := by
    refine ContinuousLinearMap.ext fun u => ?_
    rw [hFdef]
    simpa using expCoordinates_fderiv_gram_zero (I := I) g p u a b
  have hFdiffAt : ∀ y ∈ ball (0 : E) ρ, DifferentiableAt ℝ F y := fun y hy =>
    (hFdiff y hy).differentiableAt (isOpen_ball.mem_nhds hy)
  have hDdiffAt : ∀ y ∈ ball (0 : E) ρ, DifferentiableAt ℝ (fun z => fderiv ℝ F z) y :=
    fun y hy => (hDdiff y hy).differentiableAt (isOpen_ball.mem_nhds hy)
  have hbound1 : ∀ y ∈ closedBall (0 : E) (ρ / 2), ‖fderiv ℝ F y‖ ≤ K * ‖y‖ := by
    intro y hy
    have h := (convex_closedBall (0 : E) (ρ / 2)).norm_image_sub_le_of_norm_fderiv_le
      (f := fun z => fderiv ℝ F z) (C := K)
      (fun z hz => hDdiffAt z (hsub hz)) (fun z hz => hK z hz)
      (mem_closedBall_self (by linarith)) hy
    simpa [hD0] using h
  -- and the mean value theorem on `F` itself over the ball of radius `‖x‖` finishes
  refine ⟨K, hK0, fun x hx => ?_⟩
  have hxb : ‖x‖ < ρ / 2 := by simpa using hx
  have hsub' : closedBall (0 : E) ‖x‖ ⊆ closedBall (0 : E) (ρ / 2) :=
    closedBall_subset_closedBall hxb.le
  have hxs : x ∈ closedBall (0 : E) ‖x‖ := by simp
  have h := (convex_closedBall (0 : E) ‖x‖).norm_image_sub_le_of_norm_fderiv_le
    (f := F) (C := K * ‖x‖)
    (fun z hz => hFdiffAt z (hsub (hsub' hz)))
    (fun z hz => by
      refine le_trans (hbound1 z (hsub' hz)) ?_
      have : ‖z‖ ≤ ‖x‖ := by simpa using hz
      exact mul_le_mul_of_nonneg_left this hK0)
    (mem_closedBall_self (norm_nonneg x)) hxs
  have hF0 : F 0 = g.metricInner p a b := by
    rw [hFdef]
    exact expGram_zero (I := I) g p a b
  rw [hF0] at h
  simp only [sub_zero, Real.norm_eq_abs] at h
  calc |expGram (I := I) g p x a b - g.metricInner p a b| = |F x - g.metricInner p a b| := rfl
    _ ≤ K * ‖x‖ * ‖x‖ := h
    _ = K * ‖x‖ ^ 2 := by ring

end PetersenLib

end
