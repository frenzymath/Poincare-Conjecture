import DoCarmoLib.Riemannian.Geodesic.FlowCInftyDependence
import DoCarmoLib.Riemannian.Exponential.MovingBaseRayODE

/-! # Do Carmo Ch. 3: chart-local geodesic existence

This module packages the coordinate-spray flow into the chart-local geodesic
notion used in the local existence theorem.  The final clause of
`geodesic_local_existence` is joint smooth dependence on the chart initial
point, initial velocity, and time.  It is obtained from the existing smooth
zero-section flow by fibre/time homogeneity of the geodesic spray.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A curve is a geodesic in the chart at `α` on `J` when its foot stays in
the chart source and its chart reading satisfies the coordinate geodesic
equation. -/
def IsChartGeodesicOn (g : RiemannianMetric I M) (α : M) (γ : ℝ → M) (J : Set ℝ) : Prop :=
  (∀ t ∈ J, γ t ∈ (chartAt H α).source) ∧
  (∀ t ∈ J, HasDerivAt (fun s => extChartAt I α (γ s))
      (deriv (fun s => extChartAt I α (γ s)) t) t) ∧
  (∀ t ∈ J, HasDerivAt (deriv (fun s => extChartAt I α (γ s)))
      (- Geodesic.chartChristoffelContraction (I := I) g α
          (deriv (fun s => extChartAt I α (γ s)) t)
          (deriv (fun s => extChartAt I α (γ s)) t)
          (extChartAt I α (γ t))) t)

namespace GeodesicLocal

/-- **Math.** **Do Carmo Ch. 3, local uniqueness of geodesics.** Two geodesics
in the chart at `α`, defined on open order-connected time sets, that have the
same position and chart velocity at a common time `t₀` agree on the entire
intersection of their time sets.

The phase lifts of their chart readings solve the same first-order coordinate
spray equation. Local ODE uniqueness makes the agreement set relatively open;
continuity makes it relatively closed, so connectedness of the overlap
propagates the initial agreement globally. -/
theorem geodesic_local_uniqueness (g : RiemannianMetric I M) (α : M) [I.Boundaryless]
    {γ₁ γ₂ : ℝ → M} {J₁ J₂ : Set ℝ} {t₀ : ℝ}
    (hJ₁ : IsOpen J₁) (hJ₁c : J₁.OrdConnected) (hJ₂ : IsOpen J₂) (hJ₂c : J₂.OrdConnected)
    (h₁ : IsChartGeodesicOn (I := I) g α γ₁ J₁)
    (h₂ : IsChartGeodesicOn (I := I) g α γ₂ J₂)
    (ht₀ : t₀ ∈ J₁ ∩ J₂) (hpos : γ₁ t₀ = γ₂ t₀)
    (hvel : deriv (fun s => extChartAt I α (γ₁ s)) t₀ =
      deriv (fun s => extChartAt I α (γ₂ s)) t₀) :
    Set.EqOn γ₁ γ₂ (J₁ ∩ J₂) := by
  classical
  set z₁ : ℝ → E × E := fun s =>
    (extChartAt I α (γ₁ s), deriv (fun s' => extChartAt I α (γ₁ s')) s) with hz₁def
  set z₂ : ℝ → E × E := fun s =>
    (extChartAt I α (γ₂ s), deriv (fun s' => extChartAt I α (γ₂ s')) s) with hz₂def
  have hz₁d : ∀ t ∈ J₁, HasDerivAt z₁
      (Geodesic.geodesicSprayCoord (I := I) g α (z₁ t).1 (z₁ t).2) t := by
    intro t ht
    exact (h₁.2.1 t ht).prodMk (h₁.2.2 t ht)
  have hz₂d : ∀ t ∈ J₂, HasDerivAt z₂
      (Geodesic.geodesicSprayCoord (I := I) g α (z₂ t).1 (z₂ t).2) t := by
    intro t ht
    exact (h₂.2.1 t ht).prodMk (h₂.2.2 t ht)
  have hz₁mem : ∀ t ∈ J₁, z₁ t ∈ (extChartAt I α).target ×ˢ (univ : Set E) := by
    intro t ht
    have hsrc : γ₁ t ∈ (extChartAt I α).source := by
      rw [extChartAt_source I]
      exact h₁.1 t ht
    exact ⟨(extChartAt I α).map_source hsrc, mem_univ _⟩
  have hJo : IsOpen (J₁ ∩ J₂) := hJ₁.inter hJ₂
  have hJc : IsPreconnected (J₁ ∩ J₂) := (hJ₁c.inter hJ₂c).isPreconnected
  haveI : PreconnectedSpace ↥(J₁ ∩ J₂) := isPreconnected_iff_preconnectedSpace.mp hJc
  set A : Set ↥(J₁ ∩ J₂) :=
    {t : ↥(J₁ ∩ J₂) | z₁ (t : ℝ) = z₂ (t : ℝ)} with hAdef
  have hA_nonempty : A.Nonempty := by
    refine ⟨⟨t₀, ht₀⟩, ?_⟩
    show (extChartAt I α (γ₁ t₀), deriv (fun s' => extChartAt I α (γ₁ s')) t₀) =
      (extChartAt I α (γ₂ t₀), deriv (fun s' => extChartAt I α (γ₂ s')) t₀)
    rw [hpos, hvel]
  have hz₁cont : ContinuousOn z₁ (J₁ ∩ J₂) := fun t ht =>
    (hz₁d t ht.1).continuousAt.continuousWithinAt
  have hz₂cont : ContinuousOn z₂ (J₁ ∩ J₂) := fun t ht =>
    (hz₂d t ht.2).continuousAt.continuousWithinAt
  have hAclosed : IsClosed A :=
    isClosed_eq (continuousOn_iff_continuous_restrict.mp hz₁cont)
      (continuousOn_iff_continuous_restrict.mp hz₂cont)
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t₁ ht₁
    have hzeq : z₁ (t₁ : ℝ) = z₂ (t₁ : ℝ) := ht₁
    have hmem₁ : z₁ (t₁ : ℝ) ∈ (extChartAt I α).target ×ˢ (univ : Set E) :=
      hz₁mem _ t₁.2.1
    have hopen : IsOpen ((extChartAt I α).target ×ˢ (univ : Set E)) :=
      (isOpen_extChartAt_target α).prod isOpen_univ
    have hC1 : ContDiffAt ℝ 1
        (fun ζ : E × E => Geodesic.geodesicSprayCoord (I := I) g α ζ.1 ζ.2)
        (z₁ (t₁ : ℝ)) :=
      ((Geodesic.contDiffOn_geodesicSprayCoord_prod (I := I) g α).contDiffAt
        (hopen.mem_nhds hmem₁)).of_le (by norm_num)
    obtain ⟨K, sLip, hsLip, hlip⟩ := hC1.exists_lipschitzOnWith
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
  have hA_univ : A = univ := IsClopen.eq_univ ⟨hAclosed, hAopen⟩ hA_nonempty
  intro t ht
  have hzt : z₁ t = z₂ t := by
    have hmem : (⟨t, ht⟩ : ↥(J₁ ∩ J₂)) ∈ (univ : Set ↥(J₁ ∩ J₂)) := mem_univ _
    rw [← hA_univ] at hmem
    exact hmem
  have hu : extChartAt I α (γ₁ t) = extChartAt I α (γ₂ t) := congrArg Prod.fst hzt
  have h1s : γ₁ t ∈ (extChartAt I α).source := by
    rw [extChartAt_source I]
    exact h₁.1 t ht.1
  have h2s : γ₂ t ∈ (extChartAt I α).source := by
    rw [extChartAt_source I]
    exact h₂.1 t ht.2
  calc
    γ₁ t = (extChartAt I α).symm (extChartAt I α (γ₁ t)) :=
      ((extChartAt I α).left_inv h1s).symm
    _ = (extChartAt I α).symm (extChartAt I α (γ₂ t)) := by rw [hu]
    _ = γ₂ t := (extChartAt I α).left_inv h2s

/-- **Math.** **Do Carmo Ch. 3, local geodesic existence.** Around every initial point
and chart velocity there is a uniform family of chart geodesics.  In chart
coordinates the family is jointly `C^∞` in `(q,w,t)`. -/
theorem geodesic_local_existence (g : RiemannianMetric I M) [I.Boundaryless]
    [CompleteSpace E] [T2Space (TangentBundle I M)] (p : M) (v : TangentSpace I p) :
    ∃ ε > 0, ∃ V₁ ∈ 𝓝 p, ∃ V₂ ∈ 𝓝 (v : E), ∃ c : M → E → ℝ → M,
      (∀ q ∈ V₁, ∀ w ∈ V₂,
        IsChartGeodesicOn (I := I) g p (c q w) (Ioo (-ε) ε) ∧
        c q w 0 = q ∧
        HasDerivAt (fun s => extChartAt I p (c q w s)) w 0) ∧
      ContDiffOn ℝ ∞
        (fun xwt : (E × E) × ℝ =>
          extChartAt I p (c ((extChartAt I p).symm xwt.1.1) xwt.1.2 xwt.2))
        (((extChartAt I p '' V₁) ×ˢ V₂) ×ˢ Ioo (-ε) ε) := by
  classical
  set x₀ : E := extChartAt I p p with hx₀def
  set z₀ : E × E := ((x₀, (0 : E)) : E × E) with hz₀def
  obtain ⟨r, ε₀, T, Z, L, σ, hT, hr, hε₀, hTε₀, hflow, hLip, -, hσ, hσC⟩ :=
    Riemannian.Geodesic.exists_uniform_geodesic_flow_contDiffAt (I := I) g p
  obtain ⟨η, ρv, b, hη, hρv, hb1, hfibre⟩ :=
    Riemannian.Exponential.geodesicFlow_fst_fibre_time_movingBase (I := I) g p hr hT hTε₀
      hflow hLip
  set vE : E := (v : E) with hvEdef
  set δ : ℝ := ‖vE‖ + 1 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  set lam : ℝ := min ρv r / (2 * δ) with hlamdef
  have hlampos : 0 < lam := by
    rw [hlamdef]
    exact div_pos (lt_min hρv hr) (by positivity)
  have hlamδ : lam * δ < min ρv r := by
    have hhalf : lam * δ = min ρv r / 2 := by
      rw [hlamdef]
      field_simp
    rw [hhalf]
    have : 0 < min ρv r := lt_min hρv hr
    linarith
  have hlamδr : lam * δ < r := lt_of_lt_of_le hlamδ (min_le_right _ _)
  have hlamδρ : lam * δ < ρv := lt_of_lt_of_le hlamδ (min_le_left _ _)
  set ν : ℝ := min η r with hνdef
  have hνpos : 0 < ν := lt_min hη hr
  set ε : ℝ := T * lam with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  set V₁ : Set M := (extChartAt I p).source ∩ extChartAt I p ⁻¹' ball x₀ ν with hV₁def
  set V₂ : Set E := ball vE 1 with hV₂def
  have hV₁ : V₁ ∈ 𝓝 p :=
    Filter.inter_mem (extChartAt_source_mem_nhds p)
      ((continuousAt_extChartAt p).preimage_mem_nhds (ball_mem_nhds _ hνpos))
  have hV₂ : V₂ ∈ 𝓝 (v : E) := ball_mem_nhds (α := E) _ one_pos
  set c : M → E → ℝ → M := fun q w t =>
    (extChartAt I p).symm ((Z ((extChartAt I p q, (t / T) • w) : E × E) T).1) with hcdef
  have hwδ : ∀ w ∈ V₂, ‖w‖ < δ := by
    intro w hw
    have h1 : ‖w‖ ≤ ‖w - vE‖ + ‖vE‖ := by simpa using norm_add_le (w - vE) vE
    have h2 : ‖w - vE‖ < 1 := by rw [← dist_eq_norm]; exact mem_ball.mp hw
    rw [hδdef]
    linarith
  have hyν : ∀ q ∈ V₁, dist (extChartAt I p q) x₀ < ν := fun q hq => mem_ball.mp hq.2
  have hscale : ∀ w ∈ V₂, ∀ t ∈ Ioo (-ε) ε, ‖(t / T) • w‖ < lam * δ := by
    intro w hw t ht
    have habs : |t| < ε := abs_lt.mpr ⟨ht.1, ht.2⟩
    have hdT : |t / T| < lam := by
      rw [abs_div, abs_of_pos hT, div_lt_iff₀ hT]
      rw [hεdef] at habs
      linarith [habs]
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_lt_mul'' hdT (hwδ w hw) (abs_nonneg _) (norm_nonneg _)
  have hmemball : ∀ q ∈ V₁, ∀ w ∈ V₂, ∀ t ∈ Ioo (-ε) ε,
      ((extChartAt I p q, (t / T) • w) : E × E) ∈ ball z₀ r := by
    intro q hq w hw t ht
    rw [mem_ball, hz₀def, Prod.dist_eq]
    refine max_lt (lt_of_lt_of_le (hyν q hq) (min_le_right _ _)) ?_
    rw [dist_zero_right]
    exact lt_trans (hscale w hw t ht) hlamδr
  have hlamw : ∀ q ∈ V₁, ∀ w ∈ V₂,
      ((extChartAt I p q, lam • w) : E × E) ∈ closedBall z₀ r := by
    intro q hq w hw
    rw [mem_closedBall, hz₀def, Prod.dist_eq]
    refine max_le (le_of_lt (lt_of_lt_of_le (hyν q hq) (min_le_right _ _))) ?_
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hlampos]
    exact le_of_lt (lt_trans (mul_lt_mul_of_pos_left (hwδ w hw) hlampos) hlamδr)
  have hzero : ∀ q ∈ V₁,
      ((extChartAt I p q, (0 : E)) : E × E) ∈ closedBall z₀ r := by
    intro q hq
    rw [mem_closedBall, hz₀def, Prod.dist_eq]
    exact max_le (le_of_lt (lt_of_lt_of_le (hyν q hq) (min_le_right _ _)))
      (by simp [hr.le])
  have hTmemIcc : T ∈ Icc (-ε₀) ε₀ := ⟨by linarith, hTε₀.le⟩
  have hTmemIoo : T ∈ Ioo (-ε₀) ε₀ := ⟨by linarith, hTε₀⟩
  have htarget : ∀ q ∈ V₁, ∀ w ∈ V₂, ∀ t ∈ Ioo (-ε) ε,
      (Z ((extChartAt I p q, (t / T) • w) : E × E) T).1 ∈ (extChartAt I p).target :=
    fun q hq w hw t ht =>
      ((hflow _ (ball_subset_closedBall (hmemball q hq w hw t ht))).2.2 T hTmemIcc).1
  have hkey : ∀ q ∈ V₁, ∀ w ∈ V₂, ∀ t ∈ Ioo (-ε) ε,
      (Z ((extChartAt I p q, (t / T) • w) : E × E) T).1
        = (Z ((extChartAt I p q, lam • w) : E × E) (t / lam)).1 := by
    intro q hq w hw t ht
    have hTlam : (0 : ℝ) < T * lam := by positivity
    have habs : |t| < ε := abs_lt.mpr ⟨ht.1, ht.2⟩
    have ha : |t / (T * lam)| < b := by
      have : |t / (T * lam)| < 1 := by
        rw [abs_div, abs_of_pos hTlam, div_lt_one hTlam]
        rw [hεdef] at habs
        linarith [habs]
      linarith
    have hρ : ‖lam • w‖ < ρv := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlampos]
      exact lt_trans (mul_lt_mul_of_pos_left (hwδ w hw) hlampos) hlamδρ
    have h1 : (t / (T * lam)) • (lam • w) = (t / T) • w := by
      rw [smul_smul]
      congr 1
      field_simp
    have h2 := hfibre (extChartAt I p q) (lam • w)
      (lt_of_lt_of_le (hyν q hq) (min_le_left _ _)) hρ (t / (T * lam)) ha
    rw [h1] at h2
    rw [h2]
    congr 2
    field_simp
  refine ⟨ε, hεpos, V₁, hV₁, V₂, hV₂, c, ?_, ?_⟩
  · intro q hq w hw
    set y : E := extChartAt I p q with hydef
    set ψ : ℝ → E × E := fun s => Z ((y, lam • w) : E × E) s with hψdef
    obtain ⟨hψ0, hψd, -⟩ := hflow _ (hlamw q hq w hw)
    have hu_eq : ∀ t ∈ Ioo (-ε) ε,
        extChartAt I p (c q w t) = (ψ (t / lam)).1 := by
      intro t ht
      simp only [hcdef]
      rw [(extChartAt I p).right_inv (htarget q hq w hw t ht)]
      exact hkey q hq w hw t ht
    have hψHD : ∀ s ∈ Ioo (-ε₀) ε₀,
        HasDerivAt ψ (Geodesic.geodesicSprayCoord (I := I) g p (ψ s).1 (ψ s).2) s :=
      fun s hs => (hψd s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have hts : ∀ t ∈ Ioo (-ε) ε, t / lam ∈ Ioo (-ε₀) ε₀ := by
      intro t ht
      have habs : |t| < ε := abs_lt.mpr ⟨ht.1, ht.2⟩
      have h : |t / lam| < T := by
        rw [abs_div, abs_of_pos hlampos, div_lt_iff₀ hlampos]
        rw [hεdef] at habs
        linarith [habs]
      have := abs_lt.mp h
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have hdiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s / lam) lam⁻¹ t := by
      intro t
      simpa using (hasDerivAt_id t).div_const lam
    have hcomp : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun s => ψ (s / lam))
        (lam⁻¹ • Geodesic.geodesicSprayCoord (I := I) g p
          (ψ (t / lam)).1 (ψ (t / lam)).2) t :=
      fun t ht => (hψHD (t / lam) (hts t ht)).scomp t (hdiv t)
    have hfst : ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (fun s => extChartAt I p (c q w s))
          (lam⁻¹ • (ψ (t / lam)).2) t := by
      intro t ht
      have h := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t (hcomp t ht)
      have heq : (fun s => extChartAt I p (c q w s)) =ᶠ[𝓝 t]
          (fun s => (ψ (s / lam)).1) := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs using hu_eq s hs
      refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
      simp [Geodesic.geodesicSprayCoord_def]
    have hderiv_eq : ∀ t ∈ Ioo (-ε) ε,
        deriv (fun s => extChartAt I p (c q w s)) t = lam⁻¹ • (ψ (t / lam)).2 :=
      fun t ht => (hfst t ht).deriv
    have h0Ioo : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hεpos⟩
    have hvel0 : HasDerivAt (fun s => extChartAt I p (c q w s)) w 0 := by
      have hψ0' : ψ 0 = ((y, lam • w) : E × E) := hψ0
      have hww : lam⁻¹ • ((y, lam • w) : E × E).2 = w := by
        show lam⁻¹ • (lam • w) = w
        rw [smul_smul, inv_mul_cancel₀ hlampos.ne', one_smul]
      have h := hfst 0 h0Ioo
      rw [zero_div, hψ0', hww] at h
      exact h
    refine ⟨⟨?_, ?_, ?_⟩, ?_, hvel0⟩
    · intro t ht
      have h := (extChartAt I p).map_target (htarget q hq w hw t ht)
      rwa [extChartAt_source I] at h
    · intro t ht
      rw [hderiv_eq t ht]
      exact hfst t ht
    · intro t ht
      have hev : deriv (fun s => extChartAt I p (c q w s)) =ᶠ[𝓝 t]
          (fun s => lam⁻¹ • (ψ (s / lam)).2) := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs using hderiv_eq s hs
      have h2 := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t (hcomp t ht)
      have h3 := h2.const_smul lam⁻¹
      refine (h3.congr_of_eventuallyEq hev).congr_deriv ?_
      rw [hderiv_eq t ht, hu_eq t ht, Geodesic.chartChristoffelContraction_smul_smul]
      simp [Geodesic.geodesicSprayCoord_def, smul_smul]
    · have hz : Z ((y, (0 : E)) : E × E) T = ((y, (0 : E)) : E × E) :=
        Riemannian.Exponential.geodesicFlow_eqOn_of_zero_velocity (I := I) g p hε₀ hflow
          (hzero q hq) T hTmemIoo
      simp only [hcdef, zero_div, zero_smul]
      rw [← hydef, hz]
      exact (extChartAt I p).left_inv hq.1
  · have hG : ContDiff ℝ ∞
        (fun xwt : (E × E) × ℝ => ((xwt.1.1, (xwt.2 / T) • xwt.1.2) : E × E)) :=
      (contDiff_fst.fst).prodMk ((contDiff_snd.div_const T).smul contDiff_fst.snd)
    have hTmem : (T : ℝ) ∈ Icc (0 : ℝ) T := ⟨hT.le, le_refl T⟩
    have hΨ : ContDiffOn ℝ ∞
        (fun z : E × E => ((σ z) ⟨T, hTmem⟩ : E × E).1) (ball z₀ r) := by
      intro z hz
      exact ((((ContinuousLinearMap.fst ℝ E E).comp
        (ContinuousMap.evalCLM ℝ (⟨T, hTmem⟩ : Icc (0 : ℝ) T))).contDiff.contDiffAt).comp z
          (hσC z hz)).contDiffWithinAt
    have hmaps : MapsTo
        (fun xwt : (E × E) × ℝ => ((xwt.1.1, (xwt.2 / T) • xwt.1.2) : E × E))
        (((extChartAt I p '' V₁) ×ˢ V₂) ×ˢ Ioo (-ε) ε) (ball z₀ r) := by
      rintro ⟨⟨x, u⟩, t⟩ ⟨⟨hx, hu⟩, ht⟩
      obtain ⟨q, hq, rfl⟩ := hx
      exact hmemball q hq u hu t ht
    have hcomp := hΨ.comp hG.contDiffOn hmaps
    refine hcomp.congr ?_
    rintro ⟨⟨x, u⟩, t⟩ ⟨⟨hx, hu⟩, ht⟩
    obtain ⟨q, hq, rfl⟩ := hx
    have hqinv : (extChartAt I p).symm (extChartAt I p q) = q :=
      (extChartAt I p).left_inv hq.1
    simp only [Function.comp_apply, hcdef, hqinv]
    rw [(extChartAt I p).right_inv (htarget q hq u hu t ht)]
    exact congrArg Prod.fst
      (hσ _ (ball_subset_closedBall (hmemball q hq u hu t ht)) ⟨T, hTmem⟩).symm

/-- **Math.** **Intrinsic initial-data neighborhood for the local geodesic
family.** Around the zero tangent vector at `p` there is a genuine
neighborhood in `T M` on which every initial datum determines a chart
geodesic for one common time interval. The curve starts at the foot of the
datum, and its initial velocity in the fixed chart at `p` is exactly the
fiber coordinate of that datum.

This is the tangent-bundle form of `geodesic_local_existence`. The key extra
point is that the simultaneous restrictions on the foot and the fiber
coordinate define a neighborhood in `T M`, rather than merely two unrelated
model-space neighborhoods. -/
theorem geodesic_local_existence_tangentBundle
    (g : RiemannianMetric I M) [I.Boundaryless]
    [CompleteSpace E] [T2Space (TangentBundle I M)] (p : M) :
    ∃ ε > 0,
      ∃ U ∈ nhds (⟨p, (0 : E)⟩ : TangentBundle I M),
        ∃ c : TangentBundle I M → ℝ → M,
          ∀ z ∈ U,
            z.proj ∈ (chartAt H p).source ∧
            IsChartGeodesicOn (I := I) g p (c z) (Ioo (-ε) ε) ∧
            c z 0 = z.proj ∧
            HasDerivAt (fun s => extChartAt I p (c z s))
              (Geodesic.chartFiberCoord (E := E) (I := I) p z) 0 := by
  classical
  obtain ⟨ε, hε, V₁, hV₁, V₂, hV₂, c₀, hc₀, _hc₀smooth⟩ :=
    geodesic_local_existence (I := I) g p (0 : E)
  change Set E at V₂
  change V₂ ∈ nhds (0 : E) at hV₂
  let z₀ : TangentBundle I M := ⟨p, (0 : E)⟩
  let U : Set (TangentBundle I M) :=
    (Bundle.TotalSpace.proj ⁻¹' V₁) ∩
      (fun z => Geodesic.chartFiberCoord (E := E) (I := I) p z) ⁻¹' V₂
  have hproj : ContinuousAt
      (Bundle.TotalSpace.proj : TangentBundle I M → M) z₀ :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt
  have hfiber : ContinuousAt
      (fun z : TangentBundle I M => Geodesic.chartFiberCoord (E := E) (I := I) p z) z₀ := by
    have hsmooth := Geodesic.contMDiffAt_trivializationAt_snd
      (I := I) p (p₀ := z₀) (by rfl)
    simpa only [Geodesic.chartFiberCoord_def] using hsmooth.continuousAt
  have hU : U ∈ nhds z₀ := by
    apply inter_mem
    · exact hproj.preimage_mem_nhds (by simpa [z₀] using hV₁)
    · apply hfiber.preimage_mem_nhds
      have hcoord₀ : Geodesic.chartFiberCoord (E := E) (I := I) p z₀ = 0 := by
        simpa only [z₀] using Geodesic.chartFiberCoord_self_zero (I := I) p
      rw [hcoord₀]
      exact hV₂
  let c : TangentBundle I M → ℝ → M := fun z =>
    c₀ z.proj (Geodesic.chartFiberCoord (E := E) (I := I) p z)
  refine ⟨ε, hε, U, by simpa [z₀] using hU, c, ?_⟩
  intro z hz
  have hzV₁ : z.proj ∈ V₁ := hz.1
  have hzV₂ : Geodesic.chartFiberCoord (E := E) (I := I) p z ∈ V₂ := hz.2
  obtain ⟨hgeo, hzero, hvel⟩ := hc₀ z.proj hzV₁
    (Geodesic.chartFiberCoord (E := E) (I := I) p z) hzV₂
  have hzeroMem : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hsrc : z.proj ∈ (chartAt H p).source := by
    rw [← hzero]
    exact hgeo.1 0 hzeroMem
  exact ⟨hsrc, by simpa only [c] using hgeo,
    by simpa only [c] using hzero, by simpa only [c] using hvel⟩

end GeodesicLocal
end Riemannian
