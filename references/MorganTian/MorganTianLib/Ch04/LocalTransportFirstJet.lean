import MorganTianLib.Ch04.RadialTensorTransport
import MorganTianLib.Ch04.LocalTransportField
import MorganTianLib.Ch02.FlowIsometryBridges
import MorganTianLib.Ch02.FrameBridge

/-!
# First covariant derivatives of canonical radial extensions

A smooth field agreeing with canonical radial parallel transport has zero
covariant derivative at the centre. The closed-interval transport equation
is compared with the derivative supplied independently by field smoothness.

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

/-- **Math.** A smooth field realizing the germ of the canonical radial
parallel extension has vanishing first covariant derivative at its centre. -/
theorem cov_eq_zero_of_eventuallyEq_localLeviCivitaTangentTransport
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
    ∀ X : SmoothVectorField I M, (g.leviCivitaConnection.cov X Z) p = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro hZ X
  let y₀ := extChartAt I p p
  have hpcoord : (extChartAt I p).symm y₀ = p :=
    (extChartAt I p).left_inv (mem_extChartAt_source p)
  have hsymm : ContinuousAt (extChartAt I p).symm y₀ :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) p).continuousOn.continuousAt
      (extChartAt_target_mem_nhds (I := I) p)
  have hagree : ∀ᶠ y in 𝓝 y₀,
      y ∈ (extChartAt I p).target ∧
      (extChartAt I p).symm y ∈ U ∧
      ∀ hq : (extChartAt I p).symm y ∈ U,
        Z ((extChartAt I p).symm y) =
          localLeviCivitaTangentTransport g p hC ⟨(extChartAt I p).symm y, hq⟩ v := by
    have hZU := (show ∀ᶠ q in 𝓝 p, q ∈ U from hU.mem_nhds hpU).and hZ
    have htend : Tendsto (extChartAt I p).symm (𝓝 y₀) (𝓝 p) := by
      simpa only [hpcoord] using hsymm.tendsto
    have hcomp := htend.eventually hZU
    filter_upwards [extChartAt_target_mem_nhds (I := I) p, hcomp] with y hy hq
    exact ⟨hy, hq⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hagree
  have htarget : Metric.ball y₀ r ⊆ (extChartAt I p).target :=
    fun y hy => (hball hy).1
  have hsmall : ∀ d : E, ‖d‖ < r →
      fderiv ℝ (fieldChartRep (I := I) p Z) y₀ d +
        chartChristoffelContraction (I := I) g p d (Z p) y₀ = 0 := by
    intro d hd
    let x := (extChartAt I p).symm (y₀ + d)
    have hy : y₀ + d ∈ Metric.ball y₀ r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hd
    have hx : extChartAt I p x = y₀ + d :=
      (extChartAt I p).right_inv (htarget hy)
    have hxball : extChartAt I p x ∈ Metric.ball y₀ r := hx ▸ hy
    let c := chartRadialCurve (I := I) p x
    let u : ℝ → E := fun s => y₀ + s • d
    have huc (s : ℝ) : c s = (extChartAt I p).symm (u s) := by
      dsimp only [c, chartRadialCurve]
      rw [hx]
      congr 1
      dsimp only [u, y₀]
      module
    have humem : ∀ s ∈ Icc (0 : ℝ) 1, u s ∈ Metric.ball y₀ r := by
      intro s hs
      have hm := (convex_ball y₀ r) (Metric.mem_ball_self hr) hy
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
    have hfield : ∀ s ∈ Icc (0 : ℝ) 1,
        fieldChartRep (I := I) p Z (u s) = chartFieldRep (I := I) c p V s := by
      intro s hs
      rw [fieldChartRep_apply_eq_tangentCoordChange Z (htarget (humem s hs))]
      rw [← huc s]
      have hZc : Z (c s) =
          localLeviCivitaTangentTransport g p hC ⟨c s, hcmem s hs⟩ v := by
        suffices hh : ∀ hq : c s ∈ U, Z (c s) =
            localLeviCivitaTangentTransport g p hC ⟨c s, hq⟩ v from hh (hcmem s hs)
        rw [huc s]
        exact (hball (humem s hs)).2.2
      rw [hZc, hVend s hs (hcmem s hs)]
      rfl
    have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have huniq : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) 1) 0 :=
      (uniqueDiffOn_Icc zero_lt_one).uniqueDiffWithinAt hzero
    obtain ⟨velocity, hvel, hpar⟩ := hV 0 hzero
    have hu : HasDerivAt u d 0 := by
      simpa [u] using (hasDerivAt_id (0 : ℝ)).smul_const d |>.const_add y₀
    have hcoord : ∀ s ∈ Icc (0 : ℝ) 1, extChartAt I p (c s) = u s := by
      intro s hs
      rw [huc s]
      exact (extChartAt I p).right_inv (htarget (humem s hs))
    have hvel' := hu.hasDerivWithinAt.congr (fun s hs => hcoord s hs) (hcoord 0 hzero)
    have hvelocity : velocity = d :=
      (hvel.derivWithin huniq).symm.trans (hvel'.derivWithin huniq)
    have hf := (contDiffAt_fieldChartRep (I := I) p Z).differentiableAt (by simp)
    have hchain : HasDerivAt (fun s => fieldChartRep (I := I) p Z (u s))
        (fderiv ℝ (fieldChartRep (I := I) p Z) y₀ d) 0 := by
      have hf' : DifferentiableAt ℝ (fieldChartRep (I := I) p Z) (u 0) := by
        simpa only [u, zero_smul, add_zero] using hf
      have hh := hf'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu
      simpa only [u, zero_smul, add_zero, Function.comp_def] using hh
    have hpar' := hpar.congr (fun s hs => hfield s hs) (hfield 0 hzero)
    have heq := (hchain.hasDerivWithinAt.derivWithin huniq).symm.trans
      (hpar'.derivWithin huniq)
    have hrep0 : chartFieldRep (I := I) c p V 0 = Z p := by
      rw [← hfield 0 hzero]
      change fieldRep (I := I) p Z ((extChartAt I p).symm (y₀ + 0 • d)) = Z p
      rw [zero_smul, add_zero, hpcoord]
      exact chartFiberCoord_mk (I := I) p (Z p)
    rw [hvelocity, hrep0, chartRadialCurve_zero] at heq
    exact eq_neg_iff_add_eq_zero.mp heq
  let dx : E := X p
  let a : ℝ := r / (2 * (‖dx‖ + 1))
  have ha : 0 < a := div_pos hr (by positivity)
  have hasmall : ‖a • dx‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    dsimp [a]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 2 * (‖dx‖ + 1))]
    nlinarith [norm_nonneg dx]
  have hz := hsmall (a • dx) hasmall
  simp only [← Jacobi.chartChristoffelBilin_apply, map_smul, smul_apply] at hz
  rw [← smul_add] at hz
  have hzero := (smul_eq_zero.mp hz).resolve_left ha.ne'
  rw [cov_apply_eq_fderiv_add_chartChristoffelContraction]
  simpa only [Jacobi.chartChristoffelBilin_apply] using hzero

/-- **Math.** Canonical radial transport of a prescribed tangent vector
admits a smooth extension with zero first covariant derivative at the centre.
The extension retains its agreement with the actual endpoint transport. -/
theorem exists_smoothVectorField_localLeviCivitaTangentTransport_cov_zero
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
      ∀ X : SmoothVectorField I M, (g.leviCivitaConnection.cov X Z) p = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨Z, hZp, hZ⟩ :=
    exists_smoothVectorField_localLeviCivitaTangentTransport g p hpU hC v
  exact ⟨Z, hZp, hZ,
    cov_eq_zero_of_eventuallyEq_localLeviCivitaTangentTransport g p hU hpU hC v Z hZ⟩

end MorganTianLib
