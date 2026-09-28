import MorganTianLib.Ch04.LocalTransportFirstJet
import MorganTianLib.Ch01.SecondCov
import MorganTianLib.Ch04.SecondCovLocality
import DoCarmoLib.Riemannian.Connection.CovariantDerivativeAlongLeviCivita

/-!
# Second covariant jets of canonical radial extensions

The radial parallel equation is compared with the covariant derivative of
the same smooth field along the ray.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Set Filter Riemannian Riemannian.Geodesic
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** At an interior point of a parallel segment, a smooth realization has
zero covariant derivative in the velocity direction. -/
theorem cov_eq_zero_of_parallelWithin_comp
    (g : RiemannianMetric I M) (alpha : M) {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {a b t : ℝ}
    (hpar : IsParallelWithinSolOn (I := I) g alpha c V a b)
    (ht : t ∈ Ioo a b)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t)
    (hsrc : c t ∈ (chartAt H alpha).source)
    (X Z : SmoothVectorField I M)
    (hX : X (c t) = DCVelocity (I := I) c t)
    (hZ : ∀ s ∈ Icc a b, Z (c s) = V s) :
    (g.leviCivitaConnection.cov X Z) (c t) = 0 := by
  have htcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  have hnhds : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  obtain ⟨v, hv, hV⟩ := hpar t htcc
  have hu := hv.hasDerivAt hnhds
  have hfield : ∀ s ∈ Icc a b,
      chartFieldRep (I := I) c alpha (fun s => Z (c s)) s =
        chartFieldRep (I := I) c alpha V s := by
    intro s hs
    change tangentCoordChange I (c s) alpha (c s) (Z (c s)) =
      tangentCoordChange I (c s) alpha (c s) (V s)
    rw [hZ s hs]
  have hfield' := (hV.congr hfield (hfield t htcc)).hasDerivAt hnhds
  rw [← Riemannian.covDerivAlong_comp_smoothVectorField g hc X Z hX]
  apply (Riemannian.covDerivAlong_eq_zero_iff_chart g alpha hc.continuousAt hsrc
    hu.differentiableAt hfield'.differentiableAt).2
  rw [Riemannian.covariantDerivCoord_def, hu.deriv, hfield'.deriv]
  rw [hfield t htcc]
  exact neg_add_cancel _

omit [I.Boundaryless] in
/-- **Math.** A chart-constant tangent vector has a global smooth realization
near the chart centre. -/
theorem exists_smoothVectorField_chartConstant_germ (p : M) (d : E) :
    ∃ D : SmoothVectorField I M, D p = d ∧
      ∀ᶠ q in 𝓝 p, D q = tangentCoordChange I p q q d := by
  let S := (extChartAt I p).source
  have hS : IsOpen S := isOpen_extChartAt_source p
  have hpS : p ∈ S := mem_extChartAt_source p
  let sigma : ∀ q : M, TangentSpace I q := fun q => tangentCoordChange I p q q d
  have hsigma : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun q => (⟨q, sigma q⟩ : TangentBundle I M)) S := by
    rw [(trivializationAt E (TangentSpace I) p).contMDiffOn_section_iff
      hS (fun q hq => by
        rwa [trivializationAt_baseSet_eq_chartAt_source, ← extChartAt_source I])]
    apply (contMDiffOn_const (c := d)).congr
    intro q hq
    exact Jacobi.tangentCoordChange_realize_self (I := I)
      (by simpa only [S, extChartAt_source] using hq) d
  obtain ⟨D, hD⟩ := exists_smoothVectorField_eventuallyEq hS hsigma hpS
  refine ⟨D, ?_, hD⟩
  rw [hD.self_of_nhds]
  exact tangentCoordChange_self (I := I) (v := d) (mem_extChartAt_source p)

omit [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The velocity of a straight chart ray is the transported
constant coordinate direction. -/
theorem dcVelocity_chartRay (p : M) (y d : E) {t : ℝ}
    (ht : y + t • d ∈ (extChartAt I p).target) :
    DCVelocity (I := I) (fun s : ℝ => (extChartAt I p).symm (y + s • d)) t =
      tangentCoordChange I p ((extChartAt I p).symm (y + t • d))
        ((extChartAt I p).symm (y + t • d)) d := by
  let u : ℝ → E := fun s => y + s • d
  have hu : HasDerivAt u d t := by
    simpa [u] using (hasDerivAt_id t).smul_const d |>.const_add y
  have hus : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) u t :=
    hu.differentiableAt.mdifferentiableAt
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I p).symm (u t) :=
    ((contMDiffOn_extChartAt_symm (I := I) (n := ∞) p) (u t) ht).contMDiffAt
      ((isOpen_extChartAt_target (I := I) p).mem_nhds ht) |>.mdifferentiableAt (by simp)
  change mfderiv 𝓘(ℝ, ℝ) I ((extChartAt I p).symm ∘ u) t 1 = _
  rw [mfderiv_comp t hsymm hus]
  change mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm (u t)
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) u t 1) = _
  have hud : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) u t 1 = d := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ u t 1 = d
    rw [hu.hasFDerivAt.fderiv]
    simp
  rw [hud]
  rw [mfderiv_extChartAt_symm_apply_eq_trivializationAt_symm ht]
  exact trivializationAt_symm_eq_tangentCoordChange (I := I) p
    (by simpa only [extChartAt_source] using (extChartAt I p).map_target ht) d

/-- **Math.** A smooth field that is zero on a one-sided chart ray has zero
covariant derivative at the centre in that ray's direction. -/
theorem cov_eq_zero_of_eq_zero_chartRay
    (g : RiemannianMetric I M) (p : M) (X W : SmoothVectorField I M)
    {a : ℝ} (ha : 0 < a) (hW : W p = 0)
    (hray : ∀ s ∈ Icc (0 : ℝ) 1,
      extChartAt I p p + s • (a • toModel (I := I) (X p)) ∈ (extChartAt I p).target)
    (hz : ∀ s ∈ Ioo (0 : ℝ) 1,
      W ((extChartAt I p).symm
        (extChartAt I p p + s • (a • toModel (I := I) (X p)))) = 0) :
    (g.leviCivitaConnection.cov X W) p = 0 := by
  let y := extChartAt I p p
  let d : E := a • toModel (I := I) (X p)
  let u : ℝ → E := fun s => y + s • d
  have hu : HasDerivAt u d 0 := by
    simpa [u] using (hasDerivAt_id (0 : ℝ)).smul_const d |>.const_add y
  have hf := (contDiffAt_fieldChartRep (I := I) p W).differentiableAt (by simp)
  have hchain : HasDerivAt (fun s => fieldChartRep (I := I) p W (u s))
      (fderiv ℝ (fieldChartRep (I := I) p W) y d) 0 := by
    have hf' : DifferentiableAt ℝ (fieldChartRep (I := I) p W) (u 0) := by
      simpa only [u, zero_smul, add_zero] using hf
    simpa only [u, zero_smul, add_zero, Function.comp_def] using
      hf'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu
  have hzero : ∀ s ∈ Icc (0 : ℝ) (1 / 2),
      fieldChartRep (I := I) p W (u s) = 0 := by
    intro s hs
    rw [fieldChartRep_apply_eq_tangentCoordChange W (hray s ⟨hs.1, by linarith [hs.2]⟩)]
    have hWs : W ((extChartAt I p).symm (u s)) = 0 := by
      rcases hs.1.eq_or_lt with hs0 | hs0
      · subst s
        change W ((extChartAt I p).symm (y + (0 : ℝ) • d)) = 0
        rw [zero_smul, add_zero]
        change W ((extChartAt I p).symm (extChartAt I p p)) = 0
        rw [(extChartAt I p).left_inv (mem_extChartAt_source p)]
        exact hW
      · exact hz s ⟨hs0, by linarith [hs.2]⟩
    rw [hWs, map_zero]
  have huniq : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) (1 / 2)) 0 :=
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1 / 2)).uniqueDiffWithinAt (by norm_num)
  have heq : fderiv ℝ (fieldChartRep (I := I) p W) y d = 0 :=
    (hchain.hasDerivWithinAt.derivWithin huniq).symm.trans
      (((hasDerivAt_const (0 : ℝ) (0 : E)).hasDerivWithinAt.congr
        hzero (hzero 0 (by norm_num))).derivWithin huniq)
  change fderiv ℝ (fieldChartRep (I := I) p W) y (a • (X p : E)) = 0 at heq
  rw [map_smul] at heq
  have hd := (smul_eq_zero.mp heq).resolve_left ha.ne'
  rw [cov_apply_eq_fderiv_add_chartChristoffelContraction, hd, hW]
  simp only [← Jacobi.chartChristoffelBilin_apply, map_zero, add_zero]

/-- **Math.** The same smooth field realizing canonical radial parallel
transport has vanishing diagonal second covariant derivative at the centre. -/
theorem secondCov_eq_zero_of_eventuallyEq_localLeviCivitaTangentTransport
    (g : RiemannianMetric I M) (p : M) {U : Set M}
    (hU : IsOpen U) (hpU : p ∈ U)
    (hC : ∀ x ∈ U, ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p x) ∧
      localTransportCurve (I := I) p x 0 = p ∧
      localTransportCurve (I := I) p x 1 = x)
    (v : TangentSpace I p) (Z : SmoothVectorField I M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (∀ᶠ q in 𝓝 p, ∀ hq : q ∈ U,
      Z q = localLeviCivitaTangentTransport g p hC ⟨q, hq⟩ v) →
    ∀ X : SmoothVectorField I M, secondCov g.leviCivitaConnection X X Z p = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro hZ X
  have hfirst := cov_eq_zero_of_eventuallyEq_localLeviCivitaTangentTransport
    g p hU hpU hC v Z hZ
  obtain ⟨D, hDp, hD⟩ := exists_smoothVectorField_chartConstant_germ
    (I := I) p (toModel (I := I) (X p))
  have hDX : D p = X p := hDp
  rw [secondCov_congr_diagonal g g.leviCivitaConnection Z hDX.symm]
  let dx := toModel (I := I) (D p)
  have hD' : ∀ᶠ q in 𝓝 p, D q = tangentCoordChange I p q q dx := by
    simpa only [dx, toModel, hDX] using hD
  let y := extChartAt I p p
  have hpcoord : (extChartAt I p).symm y = p :=
    (extChartAt I p).left_inv (mem_extChartAt_source p)
  have hsymm : ContinuousAt (extChartAt I p).symm y :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) p).continuousOn.continuousAt
      (extChartAt_target_mem_nhds (I := I) p)
  have hagree : ∀ᶠ w in 𝓝 y,
      w ∈ (extChartAt I p).target ∧
      (extChartAt I p).symm w ∈ U ∧
      D ((extChartAt I p).symm w) =
        tangentCoordChange I p ((extChartAt I p).symm w) ((extChartAt I p).symm w) dx ∧
      ∀ hq : (extChartAt I p).symm w ∈ U,
        Z ((extChartAt I p).symm w) =
          localLeviCivitaTangentTransport g p hC ⟨(extChartAt I p).symm w, hq⟩ v := by
    have hZU := (show ∀ᶠ q in 𝓝 p, q ∈ U from hU.mem_nhds hpU).and (hD'.and hZ)
    have htend : Tendsto (extChartAt I p).symm (𝓝 y) (𝓝 p) := by
      simpa only [hpcoord] using hsymm.tendsto
    filter_upwards [extChartAt_target_mem_nhds (I := I) p, htend.eventually hZU]
      with w hw hq
    exact ⟨hw, hq⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hagree
  have htarget : Metric.ball y r ⊆ (extChartAt I p).target :=
    fun w hw => (hball hw).1
  let a : ℝ := r / (2 * (‖dx‖ + 1))
  have ha : 0 < a := div_pos hr (by positivity)
  let d : E := a • dx
  have hd : ‖d‖ < r := by
    rw [show ‖d‖ = |a| * ‖dx‖ from norm_smul a dx, abs_of_pos ha]
    dsimp [a]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 2 * (‖dx‖ + 1))]
    nlinarith [norm_nonneg dx]
  let x := (extChartAt I p).symm (y + d)
  have hy : y + d ∈ Metric.ball y r := by
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hd
  have hx : extChartAt I p x = y + d := (extChartAt I p).right_inv (htarget hy)
  have hxball : extChartAt I p x ∈ Metric.ball y r := hx ▸ hy
  let c := chartRadialCurve (I := I) p x
  let u : ℝ → E := fun s => y + s • d
  have huc (s : ℝ) : c s = (extChartAt I p).symm (u s) := by
    dsimp only [c, chartRadialCurve]
    rw [hx]
    congr 1
    dsimp only [u, y]
    module
  have humem : ∀ s ∈ Icc (0 : ℝ) 1, u s ∈ Metric.ball y r := by
    intro s hs
    have hm := (convex_ball y r) (Metric.mem_ball_self hr) hy
      (sub_nonneg.mpr hs.2) hs.1 (sub_add_cancel 1 s)
    convert hm using 1
    dsimp [u]
    module
  have hcmem : ∀ s ∈ Icc (0 : ℝ) 1, c s ∈ U := by
    intro s hs
    rw [huc s]
    exact (hball (humem s hs)).2.1
  obtain ⟨V, hV, _, hVend⟩ :=
    exists_radial_parallel_localLeviCivitaTangentTransport g p x hr htarget hxball hC v
  have hZc : ∀ s ∈ Icc (0 : ℝ) 1, Z (c s) = V s := by
    intro s hs
    have hh := (hball (humem s hs)).2.2.2
    rw [← huc s] at hh
    rw [hh (hcmem s hs), hVend s hs (hcmem s hs)]
  have hcovray : ∀ s ∈ Ioo (0 : ℝ) 1, (g.leviCivitaConnection.cov D Z) (c s) = 0 := by
    intro s hs
    have hscc : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
    have hcs : MDifferentiableAt 𝓘(ℝ, ℝ) I c s :=
      ((contMDiffOn_chartRadialCurve p x hr htarget hxball) s hscc).contMDiffAt
        (Icc_mem_nhds hs.1 hs.2) |>.mdifferentiableAt (by simp)
    have hsrc : c s ∈ (chartAt H p).source :=
      chartRadialCurve_mem_source p x hr htarget hxball hscc
    let aD := SmoothVectorField.smul (fun _ : M => a) contMDiff_const D
    have haD : aD (c s) = DCVelocity (I := I) c s := by
      change a • D (c s) = _
      have hcfun : c = fun s : ℝ => (extChartAt I p).symm (y + s • d) := funext huc
      rw [hcfun, dcVelocity_chartRay p y d (htarget (humem s hscc))]
      rw [(hball (humem s hscc)).2.2.1]
      change a • tangentCoordChange I p ((extChartAt I p).symm (u s))
        ((extChartAt I p).symm (u s)) dx =
          tangentCoordChange I p ((extChartAt I p).symm (u s))
            ((extChartAt I p).symm (u s)) (a • dx)
      exact (map_smul _ a dx).symm
    have hz := cov_eq_zero_of_parallelWithin_comp g p hV hs hcs hsrc aD Z haD hZc
    change (g.leviCivitaConnection.cov
      (SmoothVectorField.smul (fun _ : M => a) contMDiff_const D) Z) (c s) = 0 at hz
    rw [g.leviCivitaConnection.smul_left] at hz
    change a • (g.leviCivitaConnection.cov D Z) (c s) = 0 at hz
    exact (smul_eq_zero.mp hz).resolve_left ha.ne'
  have houter : (g.leviCivitaConnection.cov D (g.leviCivitaConnection.cov D Z)) p = 0 := by
    apply cov_eq_zero_of_eq_zero_chartRay g p D (g.leviCivitaConnection.cov D Z)
      ha (hfirst D)
    · exact fun s hs => htarget (humem s hs)
    · intro s hs
      rw [← huc s]
      exact hcovray s hs
  rw [secondCov_apply, houter, hfirst, sub_self]

/-- **Math.** A canonical radial parallel extension admits a smooth realization
retaining both its transport germ and its zero first and diagonal second jets. -/
theorem exists_smoothVectorField_localLeviCivitaTangentTransport_secondCov_zero
    (g : RiemannianMetric I M) (p : M) {U : Set M}
    (hU : IsOpen U) (hpU : p ∈ U)
    (hC : ∀ x ∈ U, ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p x) ∧
      localTransportCurve (I := I) p x 0 = p ∧
      localTransportCurve (I := I) p x 1 = x)
    (v : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ Z : SmoothVectorField I M, Z p = v ∧
      (∀ᶠ q in 𝓝 p, ∀ hq : q ∈ U,
        Z q = localLeviCivitaTangentTransport g p hC ⟨q, hq⟩ v) ∧
      (∀ X : SmoothVectorField I M, (g.leviCivitaConnection.cov X Z) p = 0) ∧
      ∀ X : SmoothVectorField I M, secondCov g.leviCivitaConnection X X Z p = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨Z, hZp, hZ, hfirst⟩ :=
    exists_smoothVectorField_localLeviCivitaTangentTransport_cov_zero g p hU hpU hC v
  exact ⟨Z, hZp, hZ, hfirst,
    secondCov_eq_zero_of_eventuallyEq_localLeviCivitaTangentTransport
      g p hU hpU hC v Z hZ⟩

end MorganTianLib
