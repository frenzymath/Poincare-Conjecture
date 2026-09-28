import MorganTianLib.Ch04.LocalTransportRegularity

/-!
# Smooth vector fields realizing canonical local transport

The canonical local Levi-Civita transport of a fixed tangent vector agrees
near the centre with a global smooth vector field. Its smooth chart
coordinates come from the parallel-transport ODE.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Set Filter Riemannian
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The canonical radial parallel extension of any tangent vector
is the germ of a global smooth vector field. The equality refers to the same
endpoint maps used to transport the tensor carrier. -/
theorem exists_smoothVectorField_localLeviCivitaTangentTransport
    (g : RiemannianMetric I M) (p : M) {U : Set M}
    (hpU : p ∈ U)
    (hC : ∀ x ∈ U, ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p x) ∧
      localTransportCurve (I := I) p x 0 = p ∧
      localTransportCurve (I := I) p x 1 = x)
    (v : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ Y : SmoothVectorField I M, Y p = v ∧
      ∀ᶠ x in 𝓝 p, ∀ hx : x ∈ U,
        Y x = localLeviCivitaTangentTransport g p hC ⟨x, hx⟩ v := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨ρ, Q, hρ, _, hQ, hQeq⟩ :=
    exists_contDiffOn_localLeviCivitaTangentTransport_coordinates g p
  let S : Set M := (chartAt H p).source ∩
    (extChartAt I p) ⁻¹' Metric.ball (extChartAt I p p) ρ
  have hS : IsOpen S := by
    dsimp only [S]
    rw [← extChartAt_source I]
    exact (continuousOn_extChartAt (I := I) p).isOpen_inter_preimage
      (isOpen_extChartAt_source p) Metric.isOpen_ball
  have hpS : p ∈ S := ⟨mem_chart_source H p, Metric.mem_ball_self hρ⟩
  let σ : ∀ x : M, TangentSpace I x := fun x =>
    tangentCoordChange I p x x (Q (extChartAt I p x) v)
  have hcoords : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun x => Q (extChartAt I p x) v) S := by
    have hQv : ContDiffOn ℝ ∞ (fun y => Q y v)
        (Metric.ball (extChartAt I p p) ρ) := hQ.clm_apply contDiffOn_const
    exact hQv.contMDiffOn.comp
      ((contMDiffOn_extChartAt (I := I) (x := p)).mono (fun x hx => hx.1))
      (fun x hx => hx.2)
  have hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, σ x⟩ : TangentBundle I M)) S := by
    rw [(trivializationAt E (TangentSpace I) p).contMDiffOn_section_iff
      hS (fun x hx => hx.1)]
    apply hcoords.congr
    intro x hx
    exact Jacobi.tangentCoordChange_realize_self (I := I) hx.1 _
  obtain ⟨Y, hY⟩ := exists_smoothVectorField_eventuallyEq hS hσ hpS
  have hagree : ∀ᶠ x in 𝓝 p, ∀ hx : x ∈ U,
      Y x = localLeviCivitaTangentTransport g p hC ⟨x, hx⟩ v := by
    filter_upwards [hY, hS.mem_nhds hpS] with x hxY hxS
    intro hxU
    rw [hxY]
    change tangentCoordChange I p x x (Q (extChartAt I p x) v) = _
    rw [← hQeq U hC ⟨x, hxU⟩ hxS.2 v]
    have hxsrc : x ∈ (extChartAt I p).source := by
      simpa only [extChartAt_source] using hxS.1
    rw [tangentCoordChange_comp (I := I)
      ⟨⟨mem_extChartAt_source x, hxsrc⟩, mem_extChartAt_source x⟩]
    exact tangentCoordChange_self (mem_extChartAt_source x)
  refine ⟨Y, ?_, hagree⟩
  rw [hagree.self_of_nhds hpU, localLeviCivitaTangentTransport_self g p hC hpU]
  rfl

/-- **Math.** Finitely many transported tangent vectors are realized by
smooth vector fields on one common neighborhood of the centre. -/
theorem exists_smoothVectorFieldFamily_localLeviCivitaTangentTransport
    {ι : Type*} [Finite ι] (g : RiemannianMetric I M) (p : M) {U : Set M}
    (hpU : p ∈ U)
    (hC : ∀ x ∈ U, ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p x) ∧
      localTransportCurve (I := I) p x 0 = p ∧
      localTransportCurve (I := I) p x 1 = x)
    (v : ι → TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ Y : ι → SmoothVectorField I M, (∀ i, Y i p = v i) ∧
      ∀ᶠ x in 𝓝 p, ∀ hx : x ∈ U, ∀ i,
        Y i x = localLeviCivitaTangentTransport g p hC ⟨x, hx⟩ (v i) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  choose Y hYp hY using fun i =>
    exists_smoothVectorField_localLeviCivitaTangentTransport g p hpU hC (v i)
  refine ⟨Y, hYp, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hY] with x hx
  exact fun hxU i => hx i hxU

end MorganTianLib
