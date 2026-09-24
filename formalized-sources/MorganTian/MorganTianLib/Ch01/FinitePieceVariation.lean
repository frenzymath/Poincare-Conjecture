import MorganTianLib.Ch01.BrokenVariationData

/-!
# Chart variations for finitely many smooth coefficient pieces

The chart partition and its piece fields are supplied independently. Matching
on each closed piece identifies a common junction field, so every varied
junction is the same geodesic in the two adjacent charts. No bound on the
number of corners is imposed.
-/

open Set Filter Riemannian Riemannian.Geodesic Module MeasureTheory
open scoped ContDiff Manifold Topology RealInnerProductSpace

noncomputable section
namespace MorganTianLib
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
  [CompleteSpace E] [T2Space (TangentBundle I M)]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Math.** Construct a genuine fixed-junction chart variation for any finite
chart partition and smooth piece fields agreeing with a common field there. -/
theorem exists_finitePieceVariationData [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) {γ : ℝ → M} {a b : ℝ}
    {e : Fin (finrank ℝ E) → ℝ → E} {W : ℕ → ℝ → 𝔼} {Wg : ℝ → 𝔼}
    {N : ℕ} {τ : ℕ → ℝ} {β : ℕ → M} {r : ℝ}
    (hN : 0 < N) (hr : 0 < r) (hmono : ∀ i, τ i < τ (i + 1))
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hW : ∀ i < N, ContDiffOn ℝ 3 (W i) (Ioo a b))
    (hmatch : ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)), Wg t = W i t)
    (hslack : ∀ i < N, ∀ t ∈ Ioo (τ i - r) (τ (i + 1) + r),
      t ∈ Ioo a b ∧ γ t ∈ (chartAt H (β i)).source ∧
        extChartAt I (β i) (γ t) ∈ interior (extChartAt I (β i)).target) :
    ∃ (u : ℕ → ℝ × ℝ → E) (ρ ε : ℝ), 0 < ρ ∧ 0 < ε ∧ ε ≤ ρ ∧
      -- regularity of each piece's chart family
      (∀ i < N, ContDiff ℝ 3 (u i)) ∧
      -- each piece stays in its chart's (extended) target on the enlarged box
      (∀ i < N, ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (τ i - ρ) (τ (i + 1) + ρ),
        u i p ∈ (extChartAt I (β i)).target) ∧
      -- the unvaried line IS `γ` read in the chart, near every time of the piece
      (∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)),
        ∀ᶠ s in 𝓝 t, u i ((0 : ℝ), s) = extChartAt I (β i) (γ s)) ∧
      -- the junction curves are the global geodesics with the prescribed initial data
      (∀ i < N, ∀ᶠ σ in 𝓝 (0 : ℝ), u i (σ, τ i) = extChartAt I (β i)
        (globalGeodesic (I := I) g hg (γ (τ i))
          ((frameFieldOf (I := I) g γ e Wg (τ i) : E)) σ)) ∧
      (∀ i < N, ∀ᶠ σ in 𝓝 (0 : ℝ), u i (σ, τ (i + 1)) = extChartAt I (β i)
        (globalGeodesic (I := I) g hg (γ (τ (i + 1)))
          ((frameFieldOf (I := I) g γ e Wg (τ (i + 1)) : E)) σ)) ∧
      -- the `∂_s`-field of the unvaried line is the piece field, read in the chart
      (∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)), ∀ᶠ s in 𝓝 t,
        fderiv ℝ (u i) ((0 : ℝ), s) ((1 : ℝ), (0 : ℝ))
          = chartVectorRep (I := I) γ (β i)
              (frameFieldOf (I := I) g γ e (W i)) s) ∧
      -- the junction geodesics stay in the chart source for small `σ` (so the chart readings
      -- above may be read *back* into `M`)
      (∀ i < N, ∀ᶠ σ in 𝓝 (0 : ℝ),
        globalGeodesic (I := I) g hg (γ (τ i))
          ((frameFieldOf (I := I) g γ e Wg (τ i) : E)) σ
            ∈ (chartAt H (β i)).source) ∧
      (∀ i < N, ∀ᶠ σ in 𝓝 (0 : ℝ),
        globalGeodesic (I := I) g hg (γ (τ (i + 1)))
          ((frameFieldOf (I := I) g γ e Wg (τ (i + 1)) : E)) σ
            ∈ (chartAt H (β i)).source) ∧
      -- `γ`'s foot stays in `(a, b)` and in the chart source over the enlarged **closed** piece
      (∀ i < N, ∀ t ∈ Icc (τ i - ρ) (τ (i + 1) + ρ),
        t ∈ Ioo a b ∧ γ t ∈ (chartAt H (β i)).source) := by
  classical
  set V : ℝ → E := frameFieldOf (I := I) g γ e Wg with hVdef
  -- ### Step 2: the per-piece construction
  have hpiece : ∀ i : ℕ, ∃ (uu : ℝ × ℝ → E) (ρ' ε' : ℝ), i < N →
      (0 < ρ' ∧ 0 < ε' ∧ ε' ≤ ρ' ∧
        ContDiff ℝ 3 uu ∧
        (∀ t ∈ Icc (τ i - ρ') (τ (i + 1) + ρ'),
          t ∈ Ioo a b ∧ γ t ∈ (chartAt H (β i)).source) ∧
        (∀ p ∈ Ioo (-ε') ε' ×ˢ Ioo (τ i - ρ') (τ (i + 1) + ρ'),
          uu p ∈ (extChartAt I (β i)).target) ∧
        (∀ t ∈ Icc (τ i) (τ (i + 1)),
          ∀ᶠ s in 𝓝 t, uu ((0 : ℝ), s) = extChartAt I (β i) (γ s)) ∧
        (∀ᶠ σ in 𝓝 (0 : ℝ), uu (σ, τ i)
          = extChartAt I (β i) (globalGeodesic (I := I) g hg (γ (τ i)) (V (τ i)) σ)) ∧
        (∀ᶠ σ in 𝓝 (0 : ℝ), uu (σ, τ (i + 1))
          = extChartAt I (β i)
              (globalGeodesic (I := I) g hg (γ (τ (i + 1))) (V (τ (i + 1))) σ)) ∧
        (∀ t ∈ Icc (τ i) (τ (i + 1)), ∀ᶠ s in 𝓝 t,
          fderiv ℝ uu ((0 : ℝ), s) ((1 : ℝ), (0 : ℝ))
            = chartVectorRep (I := I) γ (β i)
                (frameFieldOf (I := I) g γ e (W i)) s) ∧
        (∀ᶠ σ in 𝓝 (0 : ℝ), globalGeodesic (I := I) g hg (γ (τ i)) (V (τ i)) σ
          ∈ (chartAt H (β i)).source) ∧
        (∀ᶠ σ in 𝓝 (0 : ℝ), globalGeodesic (I := I) g hg (γ (τ (i + 1))) (V (τ (i + 1))) σ
          ∈ (chartAt H (β i)).source)) := by
    intro i
    by_cases hi : i < N
    swap
    · exact ⟨fun _ => 0, 1, 1, fun hc => absurd hc hi⟩
    -- the enlarged open piece, and its half-size closed companion
    set L : ℝ := τ i with hL
    set R : ℝ := τ (i + 1) with hR
    have hLR : L < R := hmono i
    have hEnl : ∀ t ∈ Ioo (L - r) (R + r),
        t ∈ Ioo a b ∧ γ t ∈ (chartAt H (β i)).source ∧
          extChartAt I (β i) (γ t) ∈ interior (extChartAt I (β i)).target :=
      hslack i hi
    have hr2 : 0 < r / 2 := by linarith
    have hJsub : Ioo (L - r / 2) (R + r / 2) ⊆ Ioo (L - r) (R + r) :=
      Ioo_subset_Ioo (by linarith) (by linarith)
    have hJclsub : Icc (L - r / 2) (R + r / 2) ⊆ Ioo (L - r) (R + r) := fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hJclab : Icc (L - r / 2) (R + r / 2) ⊆ Icc a b := fun t ht =>
      Ioo_subset_Icc_self ((hEnl t (hJclsub ht)).1)
    have hJclsrc : ∀ t ∈ Icc (L - r / 2) (R + r / 2), γ t ∈ (chartAt H (β i)).source :=
      fun t ht => (hEnl t (hJclsub ht)).2.1
    -- (a) the chart reading of the geodesic is `C³` on the open enlarged piece
    have hŷ : ContDiffOn ℝ 3 (fun t => extChartAt I (β i) (γ t))
        (Ioo (L - r / 2) (R + r / 2)) := by
      have := contDiffOn_chartReading_of_isGeodesicOn (I := I) g
        (J := Ioo (L - r / 2) (R + r / 2)) (β := β i) isOpen_Ioo
        (fun t ht => hgeo t (hJclab (Ioo_subset_Icc_self ht)))
        (fun t ht => hγc t (hJclab (Ioo_subset_Icc_self ht)))
        (fun t ht => hJclsrc t (Ioo_subset_Icc_self ht)) 3
      exact this
    -- (b) the chart reading of the piece field is `C³` there
    have hWhalf : ContDiffOn ℝ 3 (W i) (Ioo (L - r / 2) (R + r / 2)) :=
      (hW i hi).mono (fun t ht => (hEnl t (hJsub ht)).1)
    have hŶ : ContDiffOn ℝ 3
        (chartVectorRep (I := I) γ (β i)
          (frameFieldOf (I := I) g γ e (W i)))
        (Ioo (L - r / 2) (R + r / 2)) :=
      contDiffOn_chartVectorRep_frameFieldOf (I := I) hPar hgeo hγc hJclab hJclsrc hWhalf
    -- (c) bump-extend both
    obtain ⟨ŷE, Vy, hŷE, hVyopen, hIccVy, hVysub, hEqy⟩ :=
      exists_contDiff_eqOn_of_contDiffOn_Ioo (n := 3) hŷ
        (by linarith : L - r / 2 < L) hLR.le (by linarith : R < R + r / 2)
    obtain ⟨ŶE, VY, hŶE, hVYopen, hIccVY, hVYsub, hEqY⟩ :=
      exists_contDiff_eqOn_of_contDiffOn_Ioo (n := 3) hŶ
        (by linarith : L - r / 2 < L) hLR.le (by linarith : R < R + r / 2)
    -- (d) the two junction geodesics, their chart readings, and their bump extensions
    have hjunc : ∀ (T : ℝ), T ∈ Ioo (L - r) (R + r) →
        ∃ (ĉ : ℝ → E) (Vc : Set ℝ), ContDiff ℝ 3 ĉ ∧ IsOpen Vc ∧ (0 : ℝ) ∈ Vc ∧
          EqOn ĉ (fun σ => extChartAt I (β i)
            (globalGeodesic (I := I) g hg (γ T) (V T) σ)) Vc ∧
          (∀ σ ∈ Vc, globalGeodesic (I := I) g hg (γ T) (V T) σ
            ∈ (chartAt H (β i)).source) := by
      intro T hT
      have hTsrc : γ T ∈ (chartAt H (β i)).source := (hEnl T hT).2.1
      set cT : ℝ → M := globalGeodesic (I := I) g hg (γ T) (V T) with hcT
      have hcT0 : cT 0 = γ T := globalGeodesic_zero (I := I) g hg (γ T) (V T)
      have hcTcont : Continuous cT := continuous_globalGeodesic (I := I) g hg (γ T) (V T)
      have hpre : cT ⁻¹' (chartAt H (β i)).source ∈ 𝓝 (0 : ℝ) :=
        (((chartAt H (β i)).open_source).preimage hcTcont).mem_nhds
          (show cT 0 ∈ (chartAt H (β i)).source by rw [hcT0]; exact hTsrc)
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
      have hballIoo : Ioo (-δ) δ ⊆ cT ⁻¹' (chartAt H (β i)).source := by
        intro σ hσ
        refine hball ?_
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
        exact ⟨hσ.1, hσ.2⟩
      have hsm : ContDiffOn ℝ 3 (fun σ => extChartAt I (β i) (cT σ)) (Ioo (-δ) δ) :=
        contDiffOn_chartReading_globalGeodesic (I := I) g hg (γ T) (V T) isOpen_Ioo
          (fun σ hσ => hballIoo hσ) 3
      obtain ⟨ĉ, Vc, hĉ, hVcopen, hIccVc, hVcsub, hEqc⟩ :=
        exists_contDiff_eqOn_of_contDiffOn_Ioo (n := 3) hsm
          (by linarith : -δ < (0 : ℝ)) (le_refl (0 : ℝ)) (by linarith : (0 : ℝ) < δ)
      exact ⟨ĉ, Vc, hĉ, hVcopen, hIccVc ⟨le_rfl, le_rfl⟩, hEqc,
        fun σ hσ => hballIoo (hVcsub hσ)⟩
    have hLmem : L ∈ Ioo (L - r) (R + r) := ⟨by linarith, by linarith⟩
    have hRmem : R ∈ Ioo (L - r) (R + r) := ⟨by linarith, by linarith⟩
    obtain ⟨ĉ₀, V₀, hĉ₀, hV₀open, hV₀0, hEq₀, hV₀src⟩ := hjunc L hLmem
    obtain ⟨ĉ₁, V₁, hĉ₁, hV₁open, hV₁0, hEq₁, hV₁src⟩ := hjunc R hRmem
    -- (e) the chart family
    set uu : ℝ × ℝ → E := chartVariation L R ŷE ŶE ĉ₀ ĉ₁ with huu
    have hne : L ≠ R := hLR.ne
    -- the chart reading of the piece field at the two endpoints is the reading of `V`
    have hVpiece : ∀ T ∈ Icc L R,
        chartVectorRep (I := I) γ (β i)
            (frameFieldOf (I := I) g γ e (W i)) T
          = chartVectorRep (I := I) γ (β i) V T := by
      intro T hT
      have h := hmatch i hi T hT
      simp only [chartVectorRep_apply, hVdef, frameFieldOf, h]
    -- (f) the four hypotheses of `chartVariation`
    have hLVy : L ∈ Vy := hIccVy ⟨le_rfl, hLR.le⟩
    have hRVy : R ∈ Vy := hIccVy ⟨hLR.le, le_rfl⟩
    have hLVY : L ∈ VY := hIccVY ⟨le_rfl, hLR.le⟩
    have hRVY : R ∈ VY := hIccVY ⟨hLR.le, le_rfl⟩
    have hjunc0 : ∀ (T : ℝ), T ∈ Icc L R → T ∈ Ioo (L - r) (R + r) → ∀ (ĉ : ℝ → E)
        (Vc : Set ℝ), IsOpen Vc → (0 : ℝ) ∈ Vc →
        EqOn ĉ (fun σ => extChartAt I (β i)
          (globalGeodesic (I := I) g hg (γ T) (V T) σ)) Vc →
        ĉ 0 = extChartAt I (β i) (γ T) ∧
          HasDerivAt ĉ (chartVectorRep (I := I) γ (β i) V T) 0 := by
      intro T _ hTe ĉ Vc hVcopen hVc0 hEqc
      have hTsrc : γ T ∈ (chartAt H (β i)).source := (hEnl T hTe).2.1
      set cT : ℝ → M := globalGeodesic (I := I) g hg (γ T) (V T) with hcT
      have hcT0 : cT 0 = γ T := globalGeodesic_zero (I := I) g hg (γ T) (V T)
      have hev : ĉ =ᶠ[𝓝 (0 : ℝ)] fun σ => extChartAt I (β i) (cT σ) := by
        filter_upwards [hVcopen.mem_nhds hVc0] with σ hσ using hEqc hσ
      constructor
      · rw [hev.eq_of_nhds, hcT0]
      · -- the chart-`β i` velocity of the junction geodesic at `σ = 0`
        have hgeoT : HasGeodesicEquationAt (I := I) g cT 0 :=
          (isGeodesic_globalGeodesic (I := I) g hg (γ T) (V T)).hasGeodesicEquationAt 0
        have hcont : ContinuousAt cT 0 :=
          (continuous_globalGeodesic (I := I) g hg (γ T) (V T)).continuousAt
        have hsrc0 : cT 0 ∈ (chartAt H (β i)).source := by rw [hcT0]; exact hTsrc
        have hD := (hgeoT.eventually_hasDerivAt_extChartAt hcont hsrc0).self_of_nhds
        have hlocal : deriv (chartLocalCurve (I := I) cT 0) 0 = V T := by
          have hread : chartLocalCurve (I := I) cT 0
              = chartReading (I := I) (γ T) cT := by
            funext σ
            simp only [chartLocalCurve, chartReading, hcT0]
          rw [hread]
          exact (hasDerivAt_chartReading_globalGeodesic (I := I) g hg (γ T) (V T)).deriv
        rw [hlocal, hcT0] at hD
        have hrep : tangentCoordChange I (γ T) (β i) (γ T) (V T)
            = chartVectorRep (I := I) γ (β i) V T := (chartVectorRep_apply _ _ _ _).symm
        rw [hrep] at hD
        exact hD.congr_of_eventuallyEq hev
    obtain ⟨hĉ₀0, hĉ₀'⟩ := hjunc0 L ⟨le_rfl, hLR.le⟩ hLmem ĉ₀ V₀ hV₀open hV₀0 hEq₀
    obtain ⟨hĉ₁0, hĉ₁'⟩ := hjunc0 R ⟨hLR.le, le_rfl⟩ hRmem ĉ₁ V₁ hV₁open hV₁0 hEq₁
    have hc₀y : ĉ₀ 0 = ŷE L := by rw [hĉ₀0, hEqy hLVy]
    have hc₁y : ĉ₁ 0 = ŷE R := by rw [hĉ₁0, hEqy hRVy]
    have hc₀Y : HasDerivAt ĉ₀ (ŶE L) 0 := by
      have : ŶE L = chartVectorRep (I := I) γ (β i) V L := by
        rw [hEqY hLVY]; exact hVpiece L ⟨le_rfl, hLR.le⟩
      rw [this]; exact hĉ₀'
    have hc₁Y : HasDerivAt ĉ₁ (ŶE R) 0 := by
      have : ŶE R = chartVectorRep (I := I) γ (β i) V R := by
        rw [hEqY hRVY]; exact hVpiece R ⟨hLR.le, le_rfl⟩
      rw [this]; exact hĉ₁'
    -- (g) regularity, and the three identification clauses
    have hcd : ContDiff ℝ 3 uu := contDiff_chartVariation hne hŷE hŶE hĉ₀ hĉ₁
    have hzero : ∀ t : ℝ, uu ((0 : ℝ), t) = ŷE t := fun t =>
      chartVariation_zero (ŷ := ŷE) (Ŷ := ŶE) hc₀y hc₁y t
    have hleft : ∀ s : ℝ, uu (s, L) = ĉ₀ s := fun s => chartVariation_left hne s
    have hright : ∀ s : ℝ, uu (s, R) = ĉ₁ s := fun s => chartVariation_right hne s
    have hfd : ∀ t : ℝ, fderiv ℝ uu ((0 : ℝ), t) ((1 : ℝ), (0 : ℝ)) = ŶE t := fun t =>
      fderiv_chartVariation_snd_zero hne hc₀y hc₁y hc₀Y hc₁Y
        ((hŷE.differentiable (by norm_num)).differentiableAt)
        ((hŶE.differentiable (by norm_num)).differentiableAt)
    -- (h) the slack radius: an enlarged closed piece inside the common agreement set
    set Vi : Set ℝ := Vy ∩ VY with hVi
    have hViopen : IsOpen Vi := hVyopen.inter hVYopen
    have hIccVi : Icc L R ⊆ Vi := fun t ht => ⟨hIccVy ht, hIccVY ht⟩
    obtain ⟨ρ', hρ', hρsub⟩ := exists_Icc_enlarged_subset hViopen hLR.le hIccVi
    have hViJ : Vi ⊆ Ioo (L - r / 2) (R + r / 2) := fun t ht => hVysub ht.1
    have hρr : ρ' < r / 2 := by
      have hmem : L - ρ' ∈ Ioo (L - r / 2) (R + r / 2) :=
        hViJ (hρsub ⟨le_rfl, by linarith⟩)
      have := hmem.1
      linarith
    have hIooρ : Ioo (L - ρ') (R + ρ') ⊆ Ioo (L - r) (R + r) :=
      Ioo_subset_Ioo (by linarith) (by linarith)
    -- (i) the tube radius
    have hmem0 : ∀ t ∈ Icc (L - ρ') (R + ρ'), uu ((0 : ℝ), t) ∈ (extChartAt I (β i)).target := by
      intro t ht
      have htVi : t ∈ Vi := hρsub ht
      rw [hzero t, hEqy htVi.1]
      have : t ∈ Ioo (L - r) (R + r) := hJsub (hViJ htVi)
      exact interior_subset (hEnl t this).2.2
    obtain ⟨ε₀, hε₀, htube⟩ :=
      exists_forall_mem_of_isCompact_of_continuous (u := uu)
        (U := (extChartAt I (β i)).target) (K := Icc (L - ρ') (R + ρ'))
        isCompact_Icc (isOpen_extChartAt_target (I := I) (β i)) hcd.continuous hmem0
    have hIccρ : Icc (L - ρ') (R + ρ') ⊆ Ioo (L - r) (R + r) := fun t ht =>
      hJsub (hViJ (hρsub ht))
    refine ⟨uu, ρ', min ε₀ ρ', fun _ => ⟨hρ', lt_min hε₀ hρ', min_le_right _ _, hcd, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩⟩
    · -- `γ` in `(a, b)` and in the chart source over the enlarged closed piece
      exact fun t ht => ⟨(hEnl t (hIccρ ht)).1, (hEnl t (hIccρ ht)).2.1⟩
    · -- the box
      rintro ⟨s, t⟩ ⟨hs, ht⟩
      have hs' : s ∈ Ioo (-ε₀) ε₀ :=
        ⟨lt_of_le_of_lt (neg_le_neg (min_le_left ε₀ ρ')) hs.1,
          hs.2.trans_le (min_le_left ε₀ ρ')⟩
      exact htube s hs' t (Ioo_subset_Icc_self ht)
    · -- the unvaried line
      intro t ht
      filter_upwards [hVyopen.mem_nhds (hIccVy ht)] with s hs
      rw [hzero s, hEqy hs]
    · -- the left junction
      filter_upwards [hV₀open.mem_nhds hV₀0] with σ hσ
      rw [hleft σ, hEq₀ hσ]
    · -- the right junction
      filter_upwards [hV₁open.mem_nhds hV₁0] with σ hσ
      rw [hright σ, hEq₁ hσ]
    · -- the `∂_s` field
      intro t ht
      filter_upwards [hVYopen.mem_nhds (hIccVY ht)] with s hs
      rw [hfd s, hEqY hs]
    · -- the left junction geodesic stays in the chart source
      filter_upwards [hV₀open.mem_nhds hV₀0] with σ hσ using hV₀src σ hσ
    · -- the right junction geodesic stays in the chart source
      filter_upwards [hV₁open.mem_nhds hV₁0] with σ hσ using hV₁src σ hσ
  -- ### Step 3: choose the per-piece data and take the minimal radii
  choose uf ρf εf hpf using hpiece
  have hrangeNE : (Finset.range N).Nonempty := ⟨0, Finset.mem_range.mpr hN⟩
  set ρ : ℝ := (Finset.range N).inf' hrangeNE ρf with hρdef
  set ε : ℝ := (Finset.range N).inf' hrangeNE εf with hεdef
  have hρle : ∀ i < N, ρ ≤ ρf i := fun i hi =>
    Finset.inf'_le _ (Finset.mem_range.mpr hi)
  have hεle : ∀ i < N, ε ≤ εf i := fun i hi =>
    Finset.inf'_le _ (Finset.mem_range.mpr hi)
  have hρpos : 0 < ρ := by
    rw [hρdef, Finset.lt_inf'_iff]
    exact fun i hi => (hpf i (Finset.mem_range.mp hi)).1
  have hεpos : 0 < ε := by
    rw [hεdef, Finset.lt_inf'_iff]
    exact fun i hi => (hpf i (Finset.mem_range.mp hi)).2.1
  have hερ : ε ≤ ρ := by
    rw [hρdef]
    refine Finset.le_inf' _ _ fun i hi => ?_
    exact (hεle i (Finset.mem_range.mp hi)).trans (hpf i (Finset.mem_range.mp hi)).2.2.1
  refine ⟨uf, ρ, ε, hρpos, hεpos, hερ,
    fun i hi => (hpf i hi).2.2.2.1, ?_, fun i hi => (hpf i hi).2.2.2.2.2.2.1,
    fun i hi => (hpf i hi).2.2.2.2.2.2.2.1, fun i hi => (hpf i hi).2.2.2.2.2.2.2.2.1,
    fun i hi => (hpf i hi).2.2.2.2.2.2.2.2.2.1,
    fun i hi => (hpf i hi).2.2.2.2.2.2.2.2.2.2.1,
    fun i hi => (hpf i hi).2.2.2.2.2.2.2.2.2.2.2, ?_⟩
  · -- the box, with the global radii
    rintro i hi ⟨s, t⟩ ⟨hs, ht⟩
    refine (hpf i hi).2.2.2.2.2.1 (s, t) ⟨?_, ?_⟩
    · exact ⟨lt_of_le_of_lt (neg_le_neg (hεle i hi)) hs.1, hs.2.trans_le (hεle i hi)⟩
    · exact ⟨by linarith [hρle i hi, ht.1], by linarith [hρle i hi, ht.2]⟩
  · -- `γ` in `(a, b)` and in the chart source, with the global radius
    intro i hi t ht
    refine (hpf i hi).2.2.2.2.1 t ⟨?_, ?_⟩
    · linarith [hρle i hi, ht.1]
    · linarith [hρle i hi, ht.2]

end MorganTianLib
