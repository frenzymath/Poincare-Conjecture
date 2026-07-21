import PetersenLib.Ch06.ParallelGlobal
import PetersenLib.Ch06.SecondVariation
import PetersenLib.Ch05.GeodesicSmoothness

/-!
# Parallel frames seeded by geodesic velocity

Petersen's Myers argument starts from a unit-speed geodesic and extends its
velocity to an orthonormal frame, then parallel-transports that frame.  This
file supplies the complete native construction:

* `exists_metricOrthonormalFrame_containing_unit` extends a prescribed unit
  tangent vector to an orthonormal frame at one point;
* `curveVelocity_isParallelSolOn` proves that the velocity of a global
  geodesic is a regular parallel field, including the chart regularity hidden
  in the classical notation `D_t c' = 0`;
* `exists_velocitySeededParallelOrthonormalFrameOn_Ioo` transports the seed
  frame and uses uniqueness of parallel transport to keep its distinguished
  member equal to the velocity throughout the interval.

This removes frame existence, preservation of orthonormality, and the
velocity-seeding identity from the remaining geometric input to Myers' theorem.
-/

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff Bundle Interval Real

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** A prescribed unit tangent vector can be completed to a
metric-orthonormal frame with that vector at any chosen index.  Extend the
orthonormal family on the singleton index set to an orthonormal basis of the
whole tangent space. -/
theorem exists_metricOrthonormalFrame_containing_unit
    (g : RiemannianMetric I M) (p : M)
    (n₀ : Fin (Module.finrank ℝ E)) (v : TangentSpace I p)
    (hv : g.metricInner p v v = 1) :
    ∃ e : Fin (Module.finrank ℝ E) → TangentSpace I p,
      e n₀ = v ∧
      ∀ i j, g.metricInner p (e i) (e j) = if i = j then (1 : ℝ) else 0 := by
  letI hm : HasMetric I M := ⟨g⟩
  let n := Module.finrank ℝ E
  let w : Fin n → TangentSpace I p := fun i => if i = n₀ then v else 0
  have hw : Orthonormal ℝ (Set.restrict ({n₀} : Set (Fin n)) w) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : i.1 = n₀ := Set.mem_singleton_iff.mp i.2
    have hj : j.1 = n₀ := Set.mem_singleton_iff.mp j.2
    have hij : i = j := Subtype.ext (hi.trans hj.symm)
    rw [if_pos hij]
    change inner ℝ (w i.1) (w j.1) = 1
    have hwi : w i.1 = v := by simp [w, hi]
    have hwj : w j.1 = v := by simp [w, hj]
    rw [hwi, hwj]
    change hm.metric.metricInner p v v = 1
    exact hv
  have hn : Module.finrank ℝ (TangentSpace I p) = Module.finrank ℝ E := rfl
  obtain ⟨b, hb⟩ := hw.exists_orthonormalBasis_extension_of_card_eq
    (ι := Fin n) (s := ({n₀} : Set (Fin n))) (v := w) (by rw [hn]; simp [n])
  refine ⟨fun i => b i, ?_, ?_⟩
  · have hbn := hb n₀ (by simp)
    simpa [w] using hbn
  · intro i j
    change hm.metric.metricInner p (b i) (b j) = if i = j then (1 : ℝ) else 0
    change inner ℝ (b i) (b j) = if i = j then (1 : ℝ) else 0
    exact orthonormal_iff_ite.mp b.orthonormal i j

/-- **Math.** The velocity field of a global geodesic is parallel in the
regular `IsParallelSolOn` sense.  Besides `D_t c' = c'' = 0`, the proof supplies
the required differentiability of the velocity's moving-foot chart reading by
transferring the geodesic ODE between nearby charts. -/
theorem curveVelocity_isParallelSolOn
    (g : RiemannianMetric I M) {c : ℝ → M}
    (hc : Continuous c) (hgeo : Geodesic.IsGeodesic (I := I) g c) :
    IsParallelSolOn (I := I) g c Set.univ (curveVelocity (I := I) c) := by
  intro t _
  have hctsrc : ∀ᶠ s in 𝓝 t, c s ∈ (extChartAt I (c t)).source :=
    hc.continuousAt.eventually_mem
      ((isOpen_extChartAt_source (I := I) (c t)).mem_nhds
        (mem_extChartAt_source (I := I) (c t)))
  have htransfer : ∀ᶠ τ in 𝓝 t,
      deriv (fun r => extChartAt I (c t) (c r)) τ =
          tangentCoordChange I (c τ) (c t) (c τ)
            (deriv (fun r => extChartAt I (c τ) (c r)) τ) ∧
        DifferentiableAt ℝ (deriv (fun r => extChartAt I (c t) (c r))) τ := by
    filter_upwards [eventually_eventually_nhds.mpr hctsrc] with τ hτsrc
    obtain ⟨vτ, aτ, hvτ, hτone, hτtwo, hτeq⟩ := hgeo τ
    have hownsrc : ∀ᶠ r in 𝓝 τ, c r ∈ (extChartAt I (c τ)).source :=
      hc.continuousAt.eventually_mem
        ((isOpen_extChartAt_source (I := I) (c τ)).mem_nhds
          (mem_extChartAt_source (I := I) (c τ)))
    have hoverlap : ∀ᶠ r in 𝓝 τ,
        c r ∈ (extChartAt I (c τ)).source ∩ (extChartAt I (c t)).source := by
      filter_upwards [hownsrc, hτsrc] with r hr₁ hr₂
      exact ⟨hr₁, hr₂⟩
    have hvτ' : HasDerivAt (fun r => extChartAt I (c τ) (c r)) vτ τ := hvτ
    have hτeq' : aτ + Geodesic.chartChristoffelContraction (I := I) g (c τ)
        (deriv (fun r => extChartAt I (c τ) (c r)) τ)
        (deriv (fun r => extChartAt I (c τ) (c r)) τ)
        (extChartAt I (c τ) (c τ)) = 0 := by
      rw [hvτ'.deriv]
      exact hτeq
    have htrans := chartReading_geodesicODE_transfer (I := I) g
      (γ := c) (t := τ) (α := c τ) (β := c t) (a := aτ)
      hoverlap hτone hτtwo hτeq'
    exact ⟨htrans.2.1, htrans.2.2.differentiableAt⟩
  have hkey : chartFieldRep (I := I) c (c t) (curveVelocity (I := I) c)
      =ᶠ[𝓝 t] deriv (fun r => extChartAt I (c t) (c r)) := by
    filter_upwards [htransfer] with τ hτ
    show tangentCoordChange I (c τ) (c t) (c τ)
        (curveVelocity (I := I) c τ) = deriv (fun r => extChartAt I (c t) (c r)) τ
    exact hτ.1.symm
  obtain ⟨_vt, _at, _hvt, htone, httwo, _hteq⟩ := hgeo t
  refine ⟨httwo.differentiableAt.congr_of_eventuallyEq hkey, ?_⟩
  have hu2 : ∀ᶠ s in 𝓝 t,
      DifferentiableAt ℝ (deriv (fun r => extChartAt I (c t) (c r))) s :=
    htransfer.mono fun _ hs => hs.2
  rw [derivAlongCurve_curveVelocity (I := I) g c t hc.continuousAt htone hu2]
  exact IsGeodesic.curveAcceleration_eq_zero hgeo t

/-- **Math.** A regular parallel field along a `C^∞` curve is `C^∞` in every
fixed chart.  Its chart reading solves the smooth nonautonomous linear ODE
`W' = -Γ(u',W)(u)`; adjoining time as a state variable turns this into an
autonomous smooth ODE, to which the single-trajectory bootstrap applies. -/
theorem IsParallelSolOn.contDiffAt_chartFieldRep_infty
    (g : RiemannianMetric I M) {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {a b t : ℝ}
    (hV : IsParallelSolOn (I := I) g c (Ioo a b) V)
    (hc : ∀ s ∈ Ioo a b, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ c s)
    (ht : t ∈ Ioo a b) :
    ContDiffAt ℝ ∞ (chartFieldRep (I := I) c (c t) V) t := by
  let α : M := c t
  let J : Set ℝ := Ioo a b ∩ interior (c ⁻¹' (chartAt H α).source)
  let u : ℝ → E := fun s => extChartAt I α (c s)
  let W : ℝ → E := chartFieldRep (I := I) c α V
  have hJopen : IsOpen J := isOpen_Ioo.inter isOpen_interior
  have htpre : c ⁻¹' (chartAt H α).source ∈ 𝓝 t :=
    (hc t ht).continuousAt.preimage_mem_nhds
      ((chartAt H α).open_source.mem_nhds (by
        change c t ∈ (chartAt H (c t)).source
        exact mem_chart_source H (c t)))
  have htJ : t ∈ J := ⟨ht, mem_interior_iff_mem_nhds.mpr htpre⟩
  have hcJ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ c J := by
    intro s hs
    exact (hc s hs.1).contMDiffWithinAt
  have hsrc : ∀ s ∈ J, c s ∈ (chartAt H α).source := by
    intro s hs
    have hs' : s ∈ c ⁻¹' (chartAt H α).source := interior_subset hs.2
    exact hs'
  have hsrc_ext : ∀ s ∈ J, c s ∈ (extChartAt I α).source := by
    intro s hs
    rw [extChartAt_source]
    exact hsrc s hs
  have hu : ContDiffOn ℝ ∞ u J :=
    contDiffOn_extChartAt_comp hcJ hsrc_ext
  have hdu : ContDiffOn ℝ ∞ (deriv u) J :=
    hu.deriv_of_isOpen hJopen le_rfl
  have hWderiv : ∀ s ∈ J, HasDerivAt W
      (-Geodesic.chartChristoffelContraction (I := I) g α
        (deriv u s) (W s) (u s)) s := by
    intro s hs
    have hcs := hc s hs.1
    have hown_u : DifferentiableAt ℝ (fun r => extChartAt I (c s) (c r)) s :=
      (contDiffAt_extChartAt_comp (I := I) le_rfl (c s) hcs
        (mem_chart_source H (c s))).differentiableAt (by simp)
    have hu_s : DifferentiableAt ℝ u s :=
      (hu.contDiffAt (hJopen.mem_nhds hs)).differentiableAt (by simp)
    have hW_s : DifferentiableAt ℝ W s := by
      exact differentiableAt_chartFieldRep_transfer (I := I) (c s) α hcs.continuousAt
        (mem_chart_source H (c s)) (hsrc s hs) hown_u (hV s hs.1).1
    exact hasDerivAt_chartFieldRep_of_parallel (I := I) g α hcs.continuousAt
      (hsrc s hs) hu_s hW_s (hV s hs.1).2
  let Φ : ℝ × E → ℝ × E := fun z =>
    (1, -Geodesic.chartChristoffelContraction (I := I) g α
      (deriv u z.1) z.2 (u z.1))
  have hΦ : ContDiffOn ℝ ∞ Φ (J ×ˢ (Set.univ : Set E)) := by
    have hy : ContDiffOn ℝ ∞ (fun z : ℝ × E => u z.1) (J ×ˢ (Set.univ : Set E)) :=
      hu.comp contDiff_fst.contDiffOn (fun z hz => hz.1)
    have hv : ContDiffOn ℝ ∞ (fun z : ℝ × E => deriv u z.1)
        (J ×ˢ (Set.univ : Set E)) :=
      hdu.comp contDiff_fst.contDiffOn (fun z hz => hz.1)
    have hw : ContDiffOn ℝ ∞ (fun z : ℝ × E => z.2) (J ×ˢ (Set.univ : Set E)) :=
      contDiff_snd.contDiffOn
    have hΓ := contDiffOn_chartChristoffelContraction_comp (I := I) g α le_rfl
      hy hv hw (fun z hz => (extChartAt I α).map_source (by
        rw [extChartAt_source]
        exact hsrc z.1 hz.1))
    exact contDiffOn_const.prodMk hΓ.neg
  have hzderiv : ∀ s ∈ J, HasDerivAt (fun r => (r, W r)) (Φ (s, W s)) s := by
    intro s hs
    exact (hasDerivAt_id s).prodMk (hWderiv s hs)
  have hzmem : MapsTo (fun s => (s, W s)) J (J ×ˢ (Set.univ : Set E)) :=
    fun s hs => ⟨hs, Set.mem_univ _⟩
  have hzsm : ContDiffOn ℝ ∞ (fun s => (s, W s)) J :=
    contDiffOn_of_hasDerivAt_smoothField hΦ hJopen hzderiv hzmem
  exact hzsm.snd.contDiffAt (hJopen.mem_nhds htJ)

/-- **Math.** A regular parallel field along a `C^∞` curve is a smooth tangent
bundle section. -/
theorem IsParallelSolOn.contMDiffAt_section_infty
    (g : RiemannianMetric I M) {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {a b t : ℝ}
    (hV : IsParallelSolOn (I := I) g c (Ioo a b) V)
    (hc : ∀ s ∈ Ioo a b, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ c s)
    (ht : t ∈ Ioo a b) :
    ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
      (fun s => (⟨c s, V s⟩ : TangentBundle I M)) t := by
  let e := trivializationAt E (TangentSpace I) (c t)
  have he : (⟨c t, V t⟩ : TangentBundle I M) ∈ e.source := by
    rw [Trivialization.mem_source, TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H (c t)
  have hiff := e.contMDiffAt_iff (IM := 𝓘(ℝ, ℝ)) (IB := I) (n := ∞)
    (f := fun s : ℝ => (⟨c s, V s⟩ : TangentBundle I M)) (x₀ := t) he
  refine hiff.mpr ⟨hc t ht, ?_⟩
  apply contMDiffAt_iff_contDiffAt.mpr
  change ContDiffAt ℝ ∞ (chartFieldRep (I := I) c (c t) V) t
  exact hV.contDiffAt_chartFieldRep_infty (I := I) g hc ht

/-- **Math.** Setwise form: a regular parallel field along a `C^∞` curve is a
smooth vector field along that curve. -/
theorem IsParallelSolOn.isVectorFieldAlong_infty
    (g : RiemannianMetric I M) {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {a b : ℝ}
    (hV : IsParallelSolOn (I := I) g c (Ioo a b) V)
    (hc : ∀ s ∈ Ioo a b, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ c s) :
    IsVectorFieldAlong (I := I) c V (Ioo a b) := by
  intro t ht
  exact (hV.contMDiffAt_section_infty (I := I) g hc ht).contMDiffWithinAt

/-- **Math.** A unit-speed global geodesic carries a parallel orthonormal frame
on every bounded open interval, with one distinguished frame vector equal to
the geodesic velocity.  The frame is seeded at `t₀`; uniqueness of the parallel
ODE identifies the transported distinguished vector with `c'`. -/
theorem exists_velocitySeededParallelOrthonormalFrameOn_Ioo
    (g : RiemannianMetric I M) {c : ℝ → M} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b)
    (hcM : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) I 2 c t)
    (hc : Continuous c) (hgeo : Geodesic.IsGeodesic (I := I) g c)
    (hunit : g.metricInner (c t₀) (curveVelocity (I := I) c t₀)
      (curveVelocity (I := I) c t₀) = 1) :
    ∃ (e : Fin (Module.finrank ℝ E) → (∀ t, TangentSpace I (c t)))
        (n₀ : Fin (Module.finrank ℝ E)),
      (∀ i, IsParallelSolOn (I := I) g c (Ioo a b) (e i)) ∧
      (∀ t ∈ Ioo a b, ∀ i j,
        g.metricInner (c t) (e i t) (e j t) = if i = j then (1 : ℝ) else 0) ∧
      (∀ t ∈ Ioo a b, e n₀ t = curveVelocity (I := I) c t) := by
  classical
  let n₀ : Fin (Module.finrank ℝ E) := Classical.choice inferInstance
  obtain ⟨e₀, hseed, horth₀⟩ :=
    exists_metricOrthonormalFrame_containing_unit (I := I) g (c t₀) n₀
      (curveVelocity (I := I) c t₀) hunit
  obtain ⟨e, he₀, hepar, heorth⟩ :=
    exists_parallelOrthonormalFrameOn_Ioo (I := I) g ht₀ hcM e₀ horth₀
  have hvel : IsParallelSolOn (I := I) g c (Ioo a b) (curveVelocity (I := I) c) :=
    (curveVelocity_isParallelSolOn (I := I) g hc hgeo).mono (subset_univ _)
  have heq : ∀ t ∈ Ioo a b, e n₀ t = curveVelocity (I := I) c t :=
    isParallelSolOn_eqOn_Ioo (I := I) g ht₀ hcM (hepar n₀) hvel (by rw [he₀ n₀, hseed])
  exact ⟨e, n₀, hepar, heorth, heq⟩

end PetersenLib

end
