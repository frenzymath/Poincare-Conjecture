import LeeLib.Ch06.HopfRinow
import LeeLib.Ch02.RiemannianCovering
import Mathlib.Analysis.Convex.Contractible
import DoCarmoLib.Riemannian.Connection.CurvaturePointwise
import DoCarmoLib.Riemannian.Manifold.HadamardComplete
import DoCarmoLib.Riemannian.Manifold.HadamardPoleClosure
import DoCarmoLib.Riemannian.Manifold.CoveringMapConclusion
import MorganTianLib.Ch01.PointwiseCurvature
import MorganTianLib.Ch01.CurvatureSectionalBound

/-!
# Lee Chapter 12: Cartan--Hadamard

This file is the Lee-facing facade for the axiom-clean Cartan--Hadamard assembly
already proved in `DoCarmoLib`.  Lee's `RiemannianMetric` is definitionally the
same mathlib structure as DoCarmo's, so the only adapter is the metric-space
instance used by the Lee presentation. Lee's curvature-tensor convention is the
negative of the convention used by the shared backend, so Lee's `K ≤ 0` appears
below as `0 ≤ ⟪R(a, c)c, a⟫`.
-/

noncomputable section

namespace LeeLib.Ch12

open Manifold
open scoped Manifold Topology ContDiff Bundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T3Space M] [ConnectedSpace M]

private def hadamardModelHomeomorph : Riemannian.HadamardModel E ≃ₜ E :=
  { toEquiv := Equiv.refl _
    continuous_toFun := continuous_id
    continuous_invFun := continuous_id }

private noncomputable instance hadamardModelContractible :
    ContractibleSpace (Riemannian.HadamardModel E) :=
  (hadamardModelHomeomorph (E := E)).contractibleSpace

private theorem leeMetric_isRiemannianDist
    (g : Riemannian.RiemannianMetric I M) :
    letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
    Riemannian.RiemannianMetric.IsRiemannianDist g := by
  letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact ⟨fun _ _ ↦ rfl⟩

variable [I.Boundaryless] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M]

/-! Lee defines sectional curvature on two-planes.  The Morgan--Tian pointwise
definition used below is its canonical extension to arbitrary pairs (the
degenerate denominator branch is zero).  The following lemma is the exact
sign conversion needed by the shared do Carmo assembly. -/

omit [ConnectedSpace M] in
/-- **Math.** Lee's nonpositive sectional-curvature hypothesis implies the
operator inequality used by the do Carmo Jacobi comparison backend. -/
theorem operator_nonpos_of_sectional_nonpos
    (g : Riemannian.RiemannianMetric I M)
    (hsec : ∀ x : M, ∀ a c : TangentSpace I x,
      MorganTianLib.sectionalCurvatureAt g g.leviCivitaConnection x a c ≤ 0) :
    ∀ x : M, ∀ a c : TangentSpace I x,
      0 ≤ g.metricInner x
        (g.leviCivitaConnection.curvatureOperatorAt x a c c) a := by
  intro x a c
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W r => g.koszulDualSection_dual X Y W r)
  have hB : Riemannian.IsAlgCurvatureForm
      (MorganTianLib.curvatureFormAt g g.leviCivitaConnection x) :=
    MorganTianLib.isAlgCurvatureForm_curvatureFormAt
      g g.leviCivitaConnection hLC x
  have hdiag := MorganTianLib.alg_curvature_le_of_sectionalCurvature_le hB
    (fun u v => hsec x u v) a c
  have hsign : MorganTianLib.curvatureFormAt g g.leviCivitaConnection x a c a c ≤ 0 := by
    simpa [MorganTianLib.sectionalCurvatureAt] using hdiag
  have hanti := MorganTianLib.curvatureFormAt_antisymm_right g g.leviCivitaConnection
    hLC.2 x a c c a
  have hform : MorganTianLib.curvatureFormAt g g.leviCivitaConnection x a c c a =
      g.metricInner x (g.leviCivitaConnection.curvatureOperatorAt x a c c) a := by
    have hM := MorganTianLib.curvatureFormAt_eq g g.leviCivitaConnection
      (MorganTianLib.extendVector x a) (MorganTianLib.extendVector x c)
      (MorganTianLib.extendVector x c) (MorganTianLib.extendVector x a) x
    simp only [MorganTianLib.extendVector_apply] at hM
    have hD := g.leviCivitaConnection.curvatureFormAt_eq g x
      (X := MorganTianLib.extendVector x a)
      (Y := MorganTianLib.extendVector x c)
      (Z := MorganTianLib.extendVector x c)
      (T := MorganTianLib.extendVector x a)
      (MorganTianLib.extendVector_apply x a)
      (MorganTianLib.extendVector_apply x c)
      (MorganTianLib.extendVector_apply x c)
      (MorganTianLib.extendVector_apply x a)
    exact hM.trans hD.symm
  rw [hform] at hanti
  linarith [hanti, hsign]

-- `HadamardModel` is definitionally the model vector space, but does not export
-- its additive zero as an instance after the wrapper is introduced.
private def hadamardOrigin : Riemannian.HadamardModel E := (0 : E)

/-- **Math.** The Hadamard model is smoothly equivalent to its underlying
Euclidean model space. -/
def cartanHadamardModelDiffeomorph :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (Riemannian.HadamardModel E) E ∞ := by
  have hlocal : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (Riemannian.HadamardModel.toModel (E := E)) := by
    intro v
    refine Riemannian.IsLocalDiffeomorphAt.congr_of_eventuallyEq
      (Riemannian.isLocalDiffeomorphAt_extChartAt (I := 𝓘(ℝ, E)) (x := v)) ?_
    filter_upwards with y
    exact (Riemannian.HadamardModel.extChartAt_hadamard v y).symm
  exact hlocal.diffeomorphOfBijective
    ⟨by intro x y h; exact h, by intro x; exact ⟨x, rfl⟩⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The Hadamard model is simply connected. -/
theorem cartanHadamardModel_simplyConnected :
    SimplyConnectedSpace (Riemannian.HadamardModel E) := by
  infer_instance

/-- **Math.** The global exponential map at `p`, bundled as a smooth map on the
Hadamard model under the Cartan--Hadamard hypotheses. -/
def cartanHadamardExpMap
    (g : Riemannian.RiemannianMetric I M) (p : M)
    (hK : ∀ x : M, ∀ a c : TangentSpace I x,
      0 ≤ g.metricInner x (g.leviCivitaConnection.curvatureOperatorAt x a c c) a) :
    letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
    CompleteSpace M → C^∞⟮𝓘(ℝ, E), Riemannian.HadamardModel E; I, M⟯ := by
  letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
  intro hcomplete
  letI : CompleteSpace M := hcomplete
  have hg : Riemannian.RiemannianMetric.IsRiemannianDist g :=
    leeMetric_isRiemannianDist g
  have hpole :=
    Riemannian.Jacobi.isLocalDiffeomorph_expMapGlobal_hadamard_of_nonpos_complete
      (E := E) (I := I) (M := M) g hg p hK
  exact ⟨fun v => Riemannian.Exponential.expMapGlobal (I := I) g hg p
    (Riemannian.HadamardModel.toModel v), hpole.contMDiff⟩

/-! The covering-map branch uses the Hadamard model with the pullback metric.
The radial geodesics supply the properness hypothesis needed by the general
covering-map conclusion. -/

/-- **Math.** On a complete connected Lee manifold of nonpositive curvature,
the exponential map at a point, expressed on the Hadamard model, is a smooth
covering map (a topological covering and a local diffeomorphism). -/
theorem cartanHadamardCovering
    (g : Riemannian.RiemannianMetric I M) (p : M)
    (hK : ∀ x : M, ∀ a c : TangentSpace I x,
      0 ≤ g.metricInner x (g.leviCivitaConnection.curvatureOperatorAt x a c c) a) :
    letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
    ∀ hcomplete : CompleteSpace M,
      LeeLib.Ch02.IsSmoothCoveringMap (cartanHadamardExpMap g p hK hcomplete) := by
  letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
  intro hcomplete
  letI : CompleteSpace M := hcomplete
  have hg : Riemannian.RiemannianMetric.IsRiemannianDist g :=
    leeMetric_isRiemannianDist g
  have hpole :=
    Riemannian.Jacobi.isLocalDiffeomorph_expMapGlobal_hadamard_of_nonpos_complete
      (E := E) (I := I) (M := M) g hg p hK
  letI gM : Riemannian.RiemannianMetric 𝓘(ℝ, E) (Riemannian.HadamardModel E) :=
    Riemannian.HadamardModel.pullbackMetric g hpole
  letI : Bundle.RiemannianBundle
      (fun x : Riemannian.HadamardModel E => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨(gM.toContinuousRiemannianMetric).toRiemannianMetric⟩
  letI : MetricSpace (Riemannian.HadamardModel E) :=
    MetricSpace.ofRiemannianMetric 𝓘(ℝ, E) (Riemannian.HadamardModel E)
  haveI hgM : gM.IsRiemannianDist := ⟨fun _ _ ↦ rfl⟩
  have hgeo : ∀ v : E,
      Riemannian.Geodesic.IsGeodesic (I := 𝓘(ℝ, E))
        (Riemannian.HadamardModel.pullbackMetric g hpole)
        (Riemannian.HadamardModel.rayCurve v) :=
    Riemannian.HadamardModel.expMap_rays_are_geodesics g hg p hpole
  have hrays : ∀ v : TangentSpace 𝓘(ℝ, E) (hadamardOrigin (E := E)),
      ∃ γ : ℝ → Riemannian.HadamardModel E, γ 0 = hadamardOrigin (E := E) ∧
        HasDerivAt
          (fun s => extChartAt 𝓘(ℝ, E) (hadamardOrigin (E := E)) (γ s)) v 0 ∧
          Continuous γ ∧
            Riemannian.Geodesic.IsGeodesic (I := 𝓘(ℝ, E)) gM γ := by
    exact Riemannian.HadamardModel.hrays_of_rayGeodesic g hpole hgeo
  letI : ProperSpace (Riemannian.HadamardModel E) :=
    Riemannian.Geodesic.properSpace_of_geodesicallyComplete_at
      (I := 𝓘(ℝ, E)) gM hgM (hadamardOrigin (E := E)) hrays
  have hexp := Riemannian.HadamardModel.dcExpandsMetric_pullbackMetric g hpole
  exact ⟨hexp.surjective hgM hpole, hexp.isCoveringMap hgM hpole, hpole⟩

/-- **Math.** Lee's Cartan--Hadamard diffeomorphism, obtained from the compiled
do Carmo assembly after installing Lee's metric-space and tangent-bundle
instances. -/
def cartanHadamardDiffeomorph
    [SimplyConnectedSpace M] [LocPathConnectedSpace M]
    (g : Riemannian.RiemannianMetric I M) (p : M)
    (hK : ∀ x : M, ∀ a c : TangentSpace I x,
      0 ≤ g.metricInner x (g.leviCivitaConnection.curvatureOperatorAt x a c c) a) :
    letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
    CompleteSpace M → Diffeomorph 𝓘(ℝ, E) I (Riemannian.HadamardModel E) M ∞ := by
  letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
  intro hcomplete
  letI : CompleteSpace M := hcomplete
  have hg : Riemannian.RiemannianMetric.IsRiemannianDist g :=
    leeMetric_isRiemannianDist g
  exact Riemannian.Jacobi.hadamardDiffeomorphOfNonpos_complete
    (E := E) (I := I) (M := M) g hg p hK

/-- **Math.** In the simply connected case, the Cartan--Hadamard
diffeomorphism has Euclidean source coordinates. -/
def cartanHadamardDiffeomorph_euclidean
    [SimplyConnectedSpace M] [LocPathConnectedSpace M]
    (g : Riemannian.RiemannianMetric I M) (p : M)
    (hK : ∀ x : M, ∀ a c : TangentSpace I x,
      0 ≤ g.metricInner x (g.leviCivitaConnection.curvatureOperatorAt x a c c) a) :
    letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
    CompleteSpace M → Diffeomorph 𝓘(ℝ, E) I E M ∞ := by
  letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
  intro hcomplete
  exact (cartanHadamardModelDiffeomorph (E := E)).symm.trans
    (cartanHadamardDiffeomorph g p hK hcomplete)

/-- **Math.** The Lee Cartan--Hadamard diffeomorphism is the exponential map
itself, viewed on the Hadamard model of the tangent space. -/
@[simp] theorem cartanHadamardDiffeomorph_coe
    [SimplyConnectedSpace M] [LocPathConnectedSpace M]
    (g : Riemannian.RiemannianMetric I M) (p : M)
    (hK : ∀ x : M, ∀ a c : TangentSpace I x,
      0 ≤ g.metricInner x (g.leviCivitaConnection.curvatureOperatorAt x a c c) a) :
    letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
    ∀ hcomplete : CompleteSpace M,
      ⇑(cartanHadamardDiffeomorph g p hK hcomplete) =
        fun v : Riemannian.HadamardModel E =>
          Riemannian.Exponential.expMapGlobal (I := I) g
            (leeMetric_isRiemannianDist g) p
            (Riemannian.HadamardModel.toModel v) := by
  letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
  intro hcomplete
  letI : CompleteSpace M := hcomplete
  have hg : Riemannian.RiemannianMetric.IsRiemannianDist g :=
    leeMetric_isRiemannianDist g
  exact Riemannian.Jacobi.hadamardDiffeomorphOfNonpos_complete_coe
    (E := E) (I := I) (M := M) g hg p hK

/-! ### Lee-facing sectional-curvature API

The declarations above expose the operator form consumed by the shared
Jacobi backend.  These wrappers state the same results with Lee's actual
sectional-curvature hypothesis, and are the declarations used by the
Chapter 12 blueprint. -/

/-- **Math.** The smooth exponential map under Lee's hypothesis
`sectionalCurvatureAt ≤ 0`. -/
def cartanHadamardExpMap_sectional
    (g : Riemannian.RiemannianMetric I M) (p : M)
    (hsec : ∀ x : M, ∀ a c : TangentSpace I x,
      MorganTianLib.sectionalCurvatureAt g g.leviCivitaConnection x a c ≤ 0) :
    letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
    CompleteSpace M → C^∞⟮𝓘(ℝ, E), Riemannian.HadamardModel E; I, M⟯ := by
  letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
  intro hcomplete
  exact cartanHadamardExpMap g p (operator_nonpos_of_sectional_nonpos g hsec) hcomplete

/-- **Math.** The exponential map is a smooth covering under nonpositive
sectional curvature. -/
theorem cartanHadamardCovering_sectional
    (g : Riemannian.RiemannianMetric I M) (p : M)
    (hsec : ∀ x : M, ∀ a c : TangentSpace I x,
      MorganTianLib.sectionalCurvatureAt g g.leviCivitaConnection x a c ≤ 0) :
    letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
    ∀ hcomplete : CompleteSpace M,
      LeeLib.Ch02.IsSmoothCoveringMap
        (cartanHadamardExpMap_sectional g p hsec hcomplete) := by
  letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
  intro hcomplete
  simpa [cartanHadamardExpMap_sectional] using
    (cartanHadamardCovering g p (operator_nonpos_of_sectional_nonpos g hsec) hcomplete)

/-- **Math.** The Cartan--Hadamard diffeomorphism under Lee's nonpositive
sectional-curvature hypothesis. -/
def cartanHadamardDiffeomorph_sectional
    [SimplyConnectedSpace M] [LocPathConnectedSpace M]
    (g : Riemannian.RiemannianMetric I M) (p : M)
    (hsec : ∀ x : M, ∀ a c : TangentSpace I x,
      MorganTianLib.sectionalCurvatureAt g g.leviCivitaConnection x a c ≤ 0) :
    letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
    CompleteSpace M → Diffeomorph 𝓘(ℝ, E) I (Riemannian.HadamardModel E) M ∞ := by
  letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
  intro hcomplete
  exact cartanHadamardDiffeomorph g p
    (operator_nonpos_of_sectional_nonpos g hsec) hcomplete

/-- **Math.** Euclidean-source form of the Cartan--Hadamard diffeomorphism
under Lee's nonpositive sectional-curvature hypothesis. -/
def cartanHadamardDiffeomorph_euclidean_sectional
    [SimplyConnectedSpace M] [LocPathConnectedSpace M]
    (g : Riemannian.RiemannianMetric I M) (p : M)
    (hsec : ∀ x : M, ∀ a c : TangentSpace I x,
      MorganTianLib.sectionalCurvatureAt g g.leviCivitaConnection x a c ≤ 0) :
    letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
    CompleteSpace M → Diffeomorph 𝓘(ℝ, E) I E M ∞ := by
  letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
  intro hcomplete
  exact cartanHadamardDiffeomorph_euclidean g p
    (operator_nonpos_of_sectional_nonpos g hsec) hcomplete

/-- **Math.** Anti-vacuity identity for the Lee-facing Cartan--Hadamard
diffeomorphism: its underlying map is the exponential map. -/
@[simp] theorem cartanHadamardDiffeomorph_sectional_coe
    [SimplyConnectedSpace M] [LocPathConnectedSpace M]
    (g : Riemannian.RiemannianMetric I M) (p : M)
    (hsec : ∀ x : M, ∀ a c : TangentSpace I x,
      MorganTianLib.sectionalCurvatureAt g g.leviCivitaConnection x a c ≤ 0) :
    letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
    ∀ hcomplete : CompleteSpace M,
      ⇑(cartanHadamardDiffeomorph_sectional g p hsec hcomplete) =
        fun v : Riemannian.HadamardModel E =>
          Riemannian.Exponential.expMapGlobal (I := I) g
            (leeMetric_isRiemannianDist g) p
            (Riemannian.HadamardModel.toModel v) := by
  letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
  intro hcomplete
  exact cartanHadamardDiffeomorph_coe g p
    (operator_nonpos_of_sectional_nonpos g hsec) hcomplete

end LeeLib.Ch12

end
