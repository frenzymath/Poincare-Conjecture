import DoCarmoLib.Riemannian.Manifold.PullbackMetric
import MorganTianLib.Ch03.RicciFlow.GaugeNaturality
import MorganTianLib.Ch03.RicciFlow.LocalExistence
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Concrete metric pullback and Ricci naturality for the Hamilton gauge

This module instantiates the coefficient-level gauge interfaces with the
smooth pullback metric.  The naturality proof follows the canonical
Levi-Civita connection through the Koszul formula and then performs the
finite-dimensional Ricci trace.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Function Riemannian

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private theorem diffeomorph_isSmoothImmersion
    (φ : Diffeomorph I I M M ∞) :
    DCSmoothImmersion (I := I) (I' := I) (φ : M → M) := by
  refine ⟨φ.isLocalDiffeomorph.contMDiff, fun p => ?_⟩
  have hcoe := φ.isLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (n := ∞) (by simp) p
  simp only [← hcoe, ContinuousLinearEquiv.coe_coe]
  exact (φ.isLocalDiffeomorph.mfderivToContinuousLinearEquiv
    (n := ∞) (by simp) p).injective

/-- **Math.** The smooth Riemannian metric obtained by pulling back `g` along `φ`. -/
noncomputable def gaugePullbackMetric
    (g : RiemannianMetric I M) (φ : Diffeomorph I I M M ∞) :
    RiemannianMetric I M := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact RiemannianMetric.pullbackOfSmoothImmersion g (φ : M → M)
    (diffeomorph_isSmoothImmersion φ)

theorem gaugePullbackMetric_metricInner
    (g : RiemannianMetric I M) (φ : Diffeomorph I I M M ∞)
    (p : M) (v w : TangentSpace I p) :
    (gaugePullbackMetric g φ).metricInner p v w =
      gaugePullbackValue g φ p v w := by
  simp only [gaugePullbackMetric,
    RiemannianMetric.pullbackOfSmoothImmersion_metricInner]
  rfl

theorem gaugePullbackMetric_dcPreservesMetric
    (g : RiemannianMetric I M) (φ : Diffeomorph I I M M ∞) :
    DCPreservesMetric (gaugePullbackMetric g φ) g (φ : M → M) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact RiemannianMetric.dcPreservesMetric_pullbackOfSmoothImmersion
    g (φ : M → M) (diffeomorph_isSmoothImmersion φ)

private theorem mfderiv_symm_leftInverse
    (φ : Diffeomorph I I M M ∞) (p : M) :
    Function.LeftInverse (mfderiv I I φ.symm (φ p)) (mfderiv I I φ p) := by
  intro v
  have h := mfderiv_comp p
    (φ.symm.contMDiff.mdifferentiableAt (by decide) (x := φ p))
    (φ.contMDiff.mdifferentiableAt (by decide) (x := p))
  have hid : (⇑φ.symm ∘ ⇑φ) = (id : M → M) :=
    funext fun q => φ.symm_apply_apply q
  rw [hid, mfderiv_id] at h
  have hv := congrArg (fun L => L v) h
  simpa using! hv.symm

private theorem mfderiv_symm_rightInverse
    (φ : Diffeomorph I I M M ∞) (p : M) :
    Function.RightInverse (mfderiv I I φ.symm (φ p)) (mfderiv I I φ p) := by
  intro v
  have h := mfderiv_comp (φ p)
    (φ.contMDiff.mdifferentiableAt (by decide) (x := φ.symm (φ p)))
    (φ.symm.contMDiff.mdifferentiableAt (by decide) (x := φ p))
  have hid : (⇑φ ∘ ⇑φ.symm) = (id : M → M) :=
    funext fun q => φ.apply_symm_apply q
  rw [hid, mfderiv_id, φ.symm_apply_apply] at h
  have hv := congrArg (fun L => L v) h
  simpa using! hv.symm

private theorem diffeomorph_mfderiv_isInvertible
    (φ : Diffeomorph I I M M ∞) (p : M) :
    (mfderiv I I φ p).IsInvertible := by
  refine ⟨φ.mfderivToContinuousLinearEquiv (by decide) p, ?_⟩
  exact Diffeomorph.mfderivToContinuousLinearEquiv_coe
    (x := p) φ (by decide)

noncomputable def gaugePushforwardVectorField
    (φ : Diffeomorph I I M M ∞) (X : SmoothVectorField I M) :
    SmoothVectorField I M where
  toFun := VectorField.mpullback I I φ.symm X
  smooth := by
    refine ContMDiff.mpullback_vectorField (I := I) (I' := I) (f := ⇑φ.symm)
      X.smooth φ.symm.contMDiff (fun p => diffeomorph_mfderiv_isInvertible φ.symm p) ?_
    simp

theorem gaugePushforwardVectorField_apply
    (φ : Diffeomorph I I M M ∞) (X : SmoothVectorField I M) (p : M) :
    gaugePushforwardVectorField φ X (φ p) = mfderiv I I φ p (X p) := by
  have hinv : (mfderiv I I φ.symm (φ p)).IsInvertible :=
    diffeomorph_mfderiv_isInvertible φ.symm (φ p)
  have hkey : (mfderiv I I φ.symm (φ p)).inverse (X p) =
      mfderiv I I φ p (X p) := by
    conv_lhs => rw [← mfderiv_symm_leftInverse φ p (X p)]
    exact hinv.inverse_apply_self _
  simp only [gaugePushforwardVectorField, VectorField.mpullback]
  rw [φ.symm_apply_apply]
  exact hkey

theorem gaugePushforwardVectorField_bracket
    (φ : Diffeomorph I I M M ∞) (X Y : SmoothVectorField I M) :
    gaugePushforwardVectorField φ (bracketField X Y) =
      bracketField (gaugePushforwardVectorField φ X)
        (gaugePushforwardVectorField φ Y) := by
  haveI hm : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hn : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top
  apply SmoothVectorField.ext
  intro q
  exact VectorField.mpullback_mlieBracket (I := I) (I' := I)
    (f := ⇑φ.symm) (n := ∞)
    (X.smooth.mdifferentiableAt (by decide))
    (Y.smooth.mdifferentiableAt (by decide))
    φ.symm.contMDiff.contMDiffAt hn

theorem gaugePushforwardVectorField_dir
    (φ : Diffeomorph I I M M ∞) (X : SmoothVectorField I M)
    (f : M → ℝ) (p : M) :
    (gaugePushforwardVectorField φ X).dir f (φ p) = X.dir (f ∘ φ) p := by
  have hφ : MDifferentiableAt I I φ p :=
    φ.contMDiff.mdifferentiableAt (by decide)
  simp only [SmoothVectorField.dir, gaugePushforwardVectorField_apply]
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (φ p)
  · rw [mfderiv_comp p hf hφ]
    rfl
  · have hcomp : ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) (f ∘ φ) p := by
      intro h
      apply hf
      have hφs : MDifferentiableAt I I φ.symm (φ p) :=
        φ.symm.contMDiff.mdifferentiableAt (by decide) (x := φ p)
      have hcompAt : MDifferentiableAt I 𝓘(ℝ, ℝ)
          (f ∘ ⇑φ) (φ.symm (φ p)) := by
        rwa [φ.symm_apply_apply]
      have h' : MDifferentiableAt I 𝓘(ℝ, ℝ)
          ((f ∘ ⇑φ) ∘ ⇑φ.symm) (φ p) := by
        exact hcompAt.comp (φ p) hφs
      have heq : ((f ∘ ⇑φ) ∘ ⇑φ.symm) = f :=
        funext fun q => by simp [Function.comp, φ.apply_symm_apply]
      rwa [heq] at h'
    rw [mfderiv_zero_of_not_mdifferentiableAt hf,
      mfderiv_zero_of_not_mdifferentiableAt hcomp]
    rfl

theorem koszulRHS_gaugePushforward
    {g g' : RiemannianMetric I M} (φ : Diffeomorph I I M M ∞)
    (hpres : DCPreservesMetric g g' φ)
    (X Y Z : SmoothVectorField I M) (p : M) :
    g'.koszulRHS (gaugePushforwardVectorField φ X)
        (gaugePushforwardVectorField φ Y)
        (gaugePushforwardVectorField φ Z) (φ p) =
      g.koszulRHS X Y Z p := by
  have hmetric : ∀ A B : SmoothVectorField I M,
      (fun q => g'.metricInner q (gaugePushforwardVectorField φ A q)
        (gaugePushforwardVectorField φ B q)) ∘ φ =
        fun q => g.metricInner q (A q) (B q) := by
    intro A B
    funext q
    simp only [Function.comp_apply, gaugePushforwardVectorField_apply]
    exact (hpres q (A q) (B q)).symm
  have hbracket : ∀ A B C : SmoothVectorField I M,
      g'.metricInner (φ p)
          (DCLieBracket (gaugePushforwardVectorField φ A)
            (gaugePushforwardVectorField φ B) (φ p))
          (gaugePushforwardVectorField φ C (φ p)) =
        g.metricInner p (DCLieBracket A B p) (C p) := by
    intro A B C
    have hb := congrArg (fun W : SmoothVectorField I M => W (φ p))
      (gaugePushforwardVectorField_bracket φ A B)
    change g'.metricInner (φ p)
        ((bracketField (gaugePushforwardVectorField φ A)
          (gaugePushforwardVectorField φ B)) (φ p))
        (gaugePushforwardVectorField φ C (φ p)) =
      g.metricInner p ((bracketField A B) p) (C p)
    rw [← hb, gaugePushforwardVectorField_apply,
      gaugePushforwardVectorField_apply]
    exact (hpres p (DCLieBracket A B p) (C p)).symm
  unfold RiemannianMetric.koszulRHS
  rw [gaugePushforwardVectorField_dir, gaugePushforwardVectorField_dir,
    gaugePushforwardVectorField_dir, hmetric, hmetric, hmetric,
    hbracket X Z Y, hbracket Y Z X, hbracket X Y Z]

private theorem canonicalLC (g : RiemannianMetric I M) :
    g.leviCivitaConnection.IsLeviCivita g :=
  g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y Z p => g.koszulDualSection_dual X Y Z p)

theorem gaugePushforward_leviCivita_cov
    {g g' : RiemannianMetric I M} (φ : Diffeomorph I I M M ∞)
    (hpres : DCPreservesMetric g g' φ) (X Y : SmoothVectorField I M) :
    gaugePushforwardVectorField φ (g.leviCivitaConnection.cov X Y) =
      g'.leviCivitaConnection.cov
        (gaugePushforwardVectorField φ X)
        (gaugePushforwardVectorField φ Y) := by
  apply SmoothVectorField.ext
  intro q
  obtain ⟨p, rfl⟩ : ∃ p : M, φ p = q :=
    ⟨φ.symm q, φ.apply_symm_apply q⟩
  refine (g'.metricInner_eq_iff_eq (φ p) _ _).mp fun W => ?_
  obtain ⟨Z, hZ⟩ := exists_smoothVectorField_eq (I := I) p
    (mfderiv I I φ.symm (φ p) W)
  have hW : W = gaugePushforwardVectorField φ Z (φ p) := by
    rw [gaugePushforwardVectorField_apply, hZ]
    exact (mfderiv_symm_rightInverse φ p W).symm
  rw [hW]
  refine mul_left_cancel₀ (two_ne_zero (α := ℝ)) ?_
  have hleft : g'.metricInner (φ p)
      (gaugePushforwardVectorField φ (g.leviCivitaConnection.cov X Y) (φ p))
      (gaugePushforwardVectorField φ Z (φ p)) =
      g.metricInner p ((g.leviCivitaConnection.cov X Y) p) (Z p) := by
    rw [gaugePushforwardVectorField_apply, gaugePushforwardVectorField_apply]
    exact (hpres p ((g.leviCivitaConnection.cov X Y) p) (Z p)).symm
  rw [hleft, g.metricInner_comm p ((g.leviCivitaConnection.cov X Y) p) (Z p),
    g'.metricInner_comm (φ p)
      ((g'.leviCivitaConnection.cov (gaugePushforwardVectorField φ X)
        (gaugePushforwardVectorField φ Y)) (φ p))
      (gaugePushforwardVectorField φ Z (φ p))]
  exact (AffineConnection.koszul_formula g g.leviCivitaConnection
    (canonicalLC g).1 (canonicalLC g).2 Y X Z p).trans
      ((koszulRHS_gaugePushforward φ hpres Y X Z p).symm.trans
        (AffineConnection.koszul_formula g' g'.leviCivitaConnection
          (canonicalLC g').1 (canonicalLC g').2
          (gaugePushforwardVectorField φ Y)
          (gaugePushforwardVectorField φ X)
          (gaugePushforwardVectorField φ Z) (φ p)).symm)

theorem gaugePushforward_leviCivita_curvature
    {g g' : RiemannianMetric I M} (φ : Diffeomorph I I M M ∞)
    (hpres : DCPreservesMetric g g' φ) (X Y Z : SmoothVectorField I M) :
    gaugePushforwardVectorField φ
        (g.leviCivitaConnection.curvature X Y Z) =
      g'.leviCivitaConnection.curvature
        (gaugePushforwardVectorField φ X)
        (gaugePushforwardVectorField φ Y)
        (gaugePushforwardVectorField φ Z) := by
  have hXZ := gaugePushforward_leviCivita_cov φ hpres X Z
  have hYZ := gaugePushforward_leviCivita_cov φ hpres Y Z
  have hfirst := gaugePushforward_leviCivita_cov φ hpres Y
    (g.leviCivitaConnection.cov X Z)
  have hsecond := gaugePushforward_leviCivita_cov φ hpres X
    (g.leviCivitaConnection.cov Y Z)
  rw [hXZ] at hfirst
  rw [hYZ] at hsecond
  have hbracket := gaugePushforwardVectorField_bracket φ X Y
  have hthird := gaugePushforward_leviCivita_cov φ hpres (bracketField X Y) Z
  rw [hbracket] at hthird
  apply SmoothVectorField.ext
  intro q
  obtain ⟨p, rfl⟩ : ∃ p : M, φ p = q :=
    ⟨φ.symm q, φ.apply_symm_apply q⟩
  have hfirst_p := congrArg (fun W : SmoothVectorField I M => W (φ p)) hfirst
  have hsecond_p := congrArg (fun W : SmoothVectorField I M => W (φ p)) hsecond
  have hthird_p := congrArg (fun W : SmoothVectorField I M => W (φ p)) hthird
  simp only [gaugePushforwardVectorField_apply] at hfirst_p hsecond_p hthird_p
  rw [gaugePushforwardVectorField_apply,
    AffineConnection.curvature_apply, AffineConnection.curvature_apply,
    map_add, map_sub, hfirst_p, hsecond_p, hthird_p]

theorem curvatureFormAt_gauge_naturality
    {g g' : RiemannianMetric I M} (φ : Diffeomorph I I M M ∞)
    (hpres : DCPreservesMetric g g' φ) (p : M)
    (x y z w : TangentSpace I p) :
    g'.leviCivitaConnection.curvatureFormAt g' (φ p)
        (mfderiv I I φ p x) (mfderiv I I φ p y)
        (mfderiv I I φ p z) (mfderiv I I φ p w) =
      g.leviCivitaConnection.curvatureFormAt g p x y z w := by
  let X : SmoothVectorField I M := AffineConnection.extendField p x
  let Y : SmoothVectorField I M := AffineConnection.extendField p y
  let Z : SmoothVectorField I M := AffineConnection.extendField p z
  let W : SmoothVectorField I M := AffineConnection.extendField p w
  have hX : X p = x := AffineConnection.extendField_apply p x
  have hY : Y p = y := AffineConnection.extendField_apply p y
  have hZ : Z p = z := AffineConnection.extendField_apply p z
  have hW : W p = w := AffineConnection.extendField_apply p w
  have hφX : gaugePushforwardVectorField φ X (φ p) = mfderiv I I φ p x := by
    rw [gaugePushforwardVectorField_apply, hX]
  have hφY : gaugePushforwardVectorField φ Y (φ p) = mfderiv I I φ p y := by
    rw [gaugePushforwardVectorField_apply, hY]
  have hφZ : gaugePushforwardVectorField φ Z (φ p) = mfderiv I I φ p z := by
    rw [gaugePushforwardVectorField_apply, hZ]
  have hφW : gaugePushforwardVectorField φ W (φ p) = mfderiv I I φ p w := by
    rw [gaugePushforwardVectorField_apply, hW]
  rw [g'.leviCivitaConnection.curvatureFormAt_eq g' (φ p)
      hφX hφY hφZ hφW,
    g.leviCivitaConnection.curvatureFormAt_eq g p hX hY hZ hW]
  have hcurv := gaugePushforward_leviCivita_curvature φ hpres X Y Z
  have hcurv_p := congrArg (fun V : SmoothVectorField I M => V (φ p)) hcurv
  unfold AffineConnection.curvatureForm
  rw [← hcurv_p, gaugePushforwardVectorField_apply,
    gaugePushforwardVectorField_apply]
  exact (hpres p ((g.leviCivitaConnection.curvature X Y Z) p) (W p)).symm

@[reducible] private noncomputable def metricFiberNormedAddCommGroup
    (g : RiemannianMetric I M) (p : M) :
    NormedAddCommGroup (TangentSpace I p) :=
  (g.toRiemannianMetric.toCore p).toNormedAddCommGroupOfTopology
    (g.toRiemannianMetric.continuousAt p)
    (g.toRiemannianMetric.isVonNBounded p)

@[reducible] private noncomputable def metricFiberInnerProductSpace
    (g : RiemannianMetric I M) (p : M) :
    letI : NormedAddCommGroup (TangentSpace I p) :=
      metricFiberNormedAddCommGroup g p
    InnerProductSpace ℝ (TangentSpace I p) :=
  InnerProductSpace.ofCoreOfTopology (g.toRiemannianMetric.toCore p)
    (g.toRiemannianMetric.continuousAt p)
    (g.toRiemannianMetric.isVonNBounded p)

/-- **Math.** Ricci curvature of the concrete pullback metric is the pullback of Ricci. -/
theorem gaugePullbackMetric_ricciTensorAt
    (g : RiemannianMetric I M) (φ : Diffeomorph I I M M ∞)
    (p : M) (v w : TangentSpace I p) :
    ricciTensorAt (gaugePullbackMetric g φ) p v w =
      gaugePullbackRicciValue g φ p v w := by
  let gp := gaugePullbackMetric g φ
  let sourceNorm := metricFiberNormedAddCommGroup gp p
  let sourceInner := metricFiberInnerProductSpace gp p
  let targetNorm := metricFiberNormedAddCommGroup g (φ p)
  let targetInner := metricFiberInnerProductSpace g (φ p)
  let L : @LinearIsometryEquiv ℝ ℝ _ _ (RingHom.id ℝ) (RingHom.id ℝ) _ _
      (TangentSpace I p) (TangentSpace I (φ p))
      (@NormedAddCommGroup.toSeminormedAddCommGroup _ sourceNorm)
      (@NormedAddCommGroup.toSeminormedAddCommGroup _ targetNorm)
      inferInstance inferInstance :=
    { toLinearEquiv :=
        (φ.mfderivToContinuousLinearEquiv (by decide) p).toLinearEquiv
      norm_map' := by
        intro u
        change Real.sqrt
            (g.metricInner (φ p) (mfderiv I I φ p u) (mfderiv I I φ p u)) =
          Real.sqrt (gp.metricInner p u u)
        exact congrArg Real.sqrt
          (gaugePullbackMetric_dcPreservesMetric g φ p u u).symm }
  let e := @stdOrthonormalBasis ℝ _ (TangentSpace I p)
    sourceNorm sourceInner inferInstance
  let e' := @OrthonormalBasis.map _ ℝ _ (TangentSpace I p)
    sourceNorm sourceInner inferInstance (TangentSpace I (φ p))
    targetNorm targetInner e L
  have hsource :=
    gp.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt gp
      (canonicalLC gp) p
  have htarget :=
    g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g
      (canonicalLC g) (φ p)
  have htrace :=
    @ricciBilin_naturality_of_basis_map
      (TangentSpace I p) (TangentSpace I (φ p))
      sourceNorm sourceInner inferInstance targetNorm targetInner inferInstance
      _ inferInstance _ _ hsource htarget e e'
      L.toLinearEquiv.toLinearMap
      (fun x y z z' => by
        change g.leviCivitaConnection.curvatureFormAt g (φ p)
            (mfderiv I I φ p x) (mfderiv I I φ p y)
            (mfderiv I I φ p z) (mfderiv I I φ p z') =
          gp.leviCivitaConnection.curvatureFormAt gp p x y z z'
        exact curvatureFormAt_gauge_naturality φ
          (gaugePullbackMetric_dcPreservesMetric g φ) p x y z z')
      (fun i => rfl) v w
  exact htrace.symm

theorem gaugePullbackMetricFamily_isRicciPullbackCompatible
    (gBar : ℝ → RiemannianMetric I M)
    (φ : ℝ → Diffeomorph I I M M ∞) (J : Set ℝ) :
    IsRicciPullbackCompatible gBar
      (fun t => gaugePullbackMetric (gBar t) (φ t)) φ J := by
  intro t ht p v w
  exact gaugePullbackMetric_ricciTensorAt (gBar t) (φ t) p v w

noncomputable def gaugePullbackMetricFamily
    (gBar : ℝ → RiemannianMetric I M)
    (φ : ℝ → Diffeomorph I I M M ∞) :
    ℝ → RiemannianMetric I M :=
  fun t => gaugePullbackMetric (gBar t) (φ t)

theorem gaugePullbackMetricFamily_isGaugePullbackOn
    (gBar : ℝ → RiemannianMetric I M)
    (φ : ℝ → Diffeomorph I I M M ∞) (J : Set ℝ) :
    IsGaugePullbackOn gBar (gaugePullbackMetricFamily gBar φ) φ J := by
  intro t ht p v w
  exact gaugePullbackMetric_metricInner (gBar t) (φ t) p v w

theorem gaugePullbackMetricFamily_zero
    (gBar : ℝ → RiemannianMetric I M)
    (φ : ℝ → Diffeomorph I I M M ∞)
    (hφ0 : φ 0 = Diffeomorph.refl I M ∞) :
    gaugePullbackMetricFamily gBar φ 0 = gBar 0 := by
  rw [gaugePullbackMetricFamily, hφ0]
  apply riemannianMetric_eq_of_metricInner_eq
  intro p v w
  rw [gaugePullbackMetric_metricInner]
  exact gaugePullbackValue_refl (gBar 0) p v w

/-- **Math.** The identity diffeomorphism realizes a zero-DeTurck solution as a
Hamilton-gauge transport.  This normalization producer isolates the general
time-dependent gauge-flow problem from the algebraic identity case. -/
noncomputable def HamiltonGaugeTransport.of_identity
    {g₀ : RiemannianMetric I M}
    (S : RicciDeTurckLocalSolution g₀)
    (hV : ∀ t ∈ (Ico 0 S.T : Set ℝ),
      S.V t = (0 : SmoothVectorField I M)) :
    HamiltonGaugeTransport S := by
  let φ : ℝ → Diffeomorph I I M M ∞ := fun _ => Diffeomorph.refl I M ∞
  refine
    { g := S.gBar
      φ := φ
      smooth_raw := S.smooth_raw
      gaugeAtZero := ?_
      pullback_raw := ?_
      transport_raw := ?_
      ricciNaturality_raw := ?_ }
  · rfl
  · intro t ht p v w
    exact (gaugePullbackValue_refl (S.gBar t) p v w).symm
  · intro t ht p v w
    have hval : gaugeTransportVariationValue S.gBar S.V φ t p v w =
        ricciDeTurckVariation (S.gBar t) (S.V t) p v w := by
      rw [gaugeTransportVariationValue_eq_neg_two_pullbackRicci]
      dsimp [φ]
      rw [gaugePullbackRicciValue_refl]
      rw [hV t ht]
      unfold ricciDeTurckVariation metricLieDerivativeAt
      rw [AffineConnection.cov_zero_right, AffineConnection.cov_zero_right]
      simp
    rw [hval]
    exact S.equation_raw t ht p v w
  · intro t ht p v w
    exact (gaugePullbackRicciValue_refl (S.gBar t) p v w).symm

noncomputable def HamiltonGaugeTransport.of_concretePullback
    {g₀ : RiemannianMetric I M}
    (S : RicciDeTurckLocalSolution g₀)
    (φ : ℝ → Diffeomorph I I M M ∞)
    (hsmooth :
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (horizontalMetricSection
          (gaugePullbackMetricFamily S.gBar φ))
        ((Set.univ : Set M) ×ˢ Ico 0 S.T))
    (hφ0 : φ 0 = Diffeomorph.refl I M ∞)
    (htransport :
      IsHamiltonGaugeTransportOn S.gBar
        (gaugePullbackMetricFamily S.gBar φ) S.V φ (Ico 0 S.T)) :
    HamiltonGaugeTransport S :=
  { g := gaugePullbackMetricFamily S.gBar φ
    φ := φ
    smooth_raw := hsmooth
    gaugeAtZero := hφ0
    pullback_raw := by
      intro t ht p v w
      exact gaugePullbackMetric_metricInner (S.gBar t) (φ t) p v w
    transport_raw := by
      intro t ht p v w
      exact htransport t ht p v w
    ricciNaturality_raw := by
      intro t ht p v w
      exact gaugePullbackMetric_ricciTensorAt (S.gBar t) (φ t) p v w }

noncomputable def HamiltonGaugeTransport.of_concretePullback_natural
    {g₀ : RiemannianMetric I M}
    (S : RicciDeTurckLocalSolution g₀)
    (φ : ℝ → Diffeomorph I I M M ∞)
    (hsmooth :
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (horizontalMetricSection
          (gaugePullbackMetricFamily S.gBar φ))
        ((Set.univ : Set M) ×ˢ Ico 0 S.T))
    (hφ0 : φ 0 = Diffeomorph.refl I M ∞)
    (htransport :
      IsHamiltonGaugeTransportOn S.gBar
        (gaugePullbackMetricFamily S.gBar φ) S.V φ (Ico 0 S.T)) :
    HamiltonGaugeTransport S :=
  HamiltonGaugeTransport.of_concretePullback S φ hsmooth hφ0 htransport

#print axioms gaugePullbackMetric_metricInner
#print axioms gaugePullbackMetric_dcPreservesMetric
#print axioms gaugePullbackMetric_ricciTensorAt
#print axioms gaugePullbackMetricFamily_isRicciPullbackCompatible
#print axioms HamiltonGaugeTransport.of_identity

end MorganTianLib

end
