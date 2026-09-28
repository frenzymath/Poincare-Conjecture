import MorganTianLib.Ch01.Chapter1BasicRemaining
import MorganTianLib.Ch01.CurvatureNormManifold
import MorganTianLib.Ch01.PointwiseCurvature
import MorganTianLib.Ch01.RiemannianMeasure
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3
import DoCarmoLib.Riemannian.Metric.RiemannianDistance

/-!
# Morgan--Tian Ch. 1: pointwise curvature under constant metric rescaling

This file extends the connection-level rescaling results in
`Chapter1BasicRemaining` to arbitrary sectional curvatures at a point.

Blueprint: `lem:metric-rescaling`.
-/

open Riemannian
open exteriorPower
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace Pointwise ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** The pointwise `(0,4)` curvature tensor is multiplied by `c`
under the constant rescaling `g ↦ c g`.
Blueprint: `lem:metric-rescaling` (item 1). -/
theorem rescaledMetric_curvatureFormAt
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (p : M) (v w z t : TangentSpace I p) :
    curvatureFormAt (rescaledMetric g c hc)
        (rescaledMetric g c hc).leviCivitaConnection p v w z t =
      c * curvatureFormAt g g.leviCivitaConnection p v w z t := by
  rw [curvatureFormAt_def, curvatureFormAt_def]
  exact rescaledMetric_curvatureForm g c hc
    (extendVector p v) (extendVector p w) (extendVector p z) (extendVector p t) p

/-- **Math.** The squared area of every tangent parallelogram is multiplied
by `c²` under the constant rescaling `g ↦ c g`.
Blueprint: `lem:metric-rescaling` (item 2). -/
theorem rescaledMetric_wedgeSq
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (p : M) (v w : TangentSpace I p) :
    (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
      Riemannian.wedgeSq v w) =
      c ^ 2 * (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩;
      Riemannian.wedgeSq v w) := by
  simp only [Riemannian.wedgeSq]
  change (rescaledMetric g c hc).metricInner p v v *
      (rescaledMetric g c hc).metricInner p w w -
      (rescaledMetric g c hc).metricInner p v w *
        (rescaledMetric g c hc).metricInner p v w =
    c ^ 2 * (g.metricInner p v v * g.metricInner p w w -
      g.metricInner p v w * g.metricInner p v w)
  rw [rescaledMetric_metricInner, rescaledMetric_metricInner,
    rescaledMetric_metricInner]
  ring

/-! ### Curvature-operator norms -/

/-- **Math.** The curvature operator, viewed as a bilinear form on the
exterior square, is multiplied by `c` under `g ↦ c g`. -/
theorem rescaledMetric_curvatureOperator
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hLC : g.leviCivitaConnection.IsLeviCivita g)
    (hLC' : (rescaledMetric g c hc).leviCivitaConnection.IsLeviCivita
      (rescaledMetric g c hc))
    (p : M) (φ ψ : ↥(ExteriorAlgebra.exteriorPower ℝ 2 (TangentSpace I p))) :
    (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
      curvatureOperator
        (isAlgCurvatureForm_curvatureFormAt (rescaledMetric g c hc)
          (rescaledMetric g c hc).leviCivitaConnection hLC' p) φ ψ) =
      c * (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩;
        curvatureOperator
          (isAlgCurvatureForm_curvatureFormAt g g.leviCivitaConnection hLC p) φ ψ) := by
  let newOp : ↥(ExteriorAlgebra.exteriorPower ℝ 2 (TangentSpace I p)) →ₗ[ℝ]
      ↥(ExteriorAlgebra.exteriorPower ℝ 2 (TangentSpace I p)) →ₗ[ℝ] ℝ :=
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(rescaledMetric g c hc).toRiemannianMetric⟩
    curvatureOperator
      (isAlgCurvatureForm_curvatureFormAt (rescaledMetric g c hc)
        (rescaledMetric g c hc).leviCivitaConnection hLC' p)
  let oldOp : ↥(ExteriorAlgebra.exteriorPower ℝ 2 (TangentSpace I p)) →ₗ[ℝ]
      ↥(ExteriorAlgebra.exteriorPower ℝ 2 (TangentSpace I p)) →ₗ[ℝ] ℝ :=
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    curvatureOperator
      (isAlgCurvatureForm_curvatureFormAt g g.leviCivitaConnection hLC p)
  have hop : newOp = c • oldOp := by
    apply exteriorPower.linearMap_ext
    ext v w
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    have hw : w = ![w 0, w 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv, hw]
    simp only [newOp, oldOp, LinearMap.compAlternatingMap_apply,
      LinearMap.smul_apply, smul_eq_mul, curvatureOperator_ιMulti]
    exact rescaledMetric_curvatureFormAt g c hc p _ _ _ _
  simpa [newOp, oldOp, LinearMap.smul_apply, smul_eq_mul] using
    congrArg (fun op => op φ ψ) hop

/-- **Math.** The metric-induced bilinear form on the exterior square is
multiplied by `c²` under `g ↦ c g`. -/
theorem rescaledMetric_wedgeInner
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) (p : M)
    (φ ψ : ↥(ExteriorAlgebra.exteriorPower ℝ 2 (TangentSpace I p))) :
    (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
      wedgeInner φ ψ) =
      c ^ 2 * (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩;
        wedgeInner φ ψ) := by
  let newOp : ↥(ExteriorAlgebra.exteriorPower ℝ 2 (TangentSpace I p)) →ₗ[ℝ]
      ↥(ExteriorAlgebra.exteriorPower ℝ 2 (TangentSpace I p)) →ₗ[ℝ] ℝ :=
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(rescaledMetric g c hc).toRiemannianMetric⟩
    wedgeInner
  let oldOp : ↥(ExteriorAlgebra.exteriorPower ℝ 2 (TangentSpace I p)) →ₗ[ℝ]
      ↥(ExteriorAlgebra.exteriorPower ℝ 2 (TangentSpace I p)) →ₗ[ℝ] ℝ :=
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    wedgeInner
  have hop : newOp = c ^ 2 • oldOp := by
    apply exteriorPower.linearMap_ext
    ext v w
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    have hw : w = ![w 0, w 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv, hw]
    simp only [newOp, oldOp, LinearMap.compAlternatingMap_apply,
      LinearMap.smul_apply, smul_eq_mul, wedgeInner_ιMulti,
      Riemannian.stdCurvForm]
    change (rescaledMetric g c hc).metricInner p (v 0) (w 0) *
          (rescaledMetric g c hc).metricInner p (v 1) (w 1) -
        (rescaledMetric g c hc).metricInner p (v 1) (w 0) *
          (rescaledMetric g c hc).metricInner p (v 0) (w 1) =
      c ^ 2 * (g.metricInner p (v 0) (w 0) * g.metricInner p (v 1) (w 1) -
        g.metricInner p (v 1) (w 0) * g.metricInner p (v 0) (w 1))
    rw [rescaledMetric_metricInner, rescaledMetric_metricInner,
      rescaledMetric_metricInner, rescaledMetric_metricInner]
    ring
  simpa [newOp, oldOp, LinearMap.smul_apply, smul_eq_mul] using
    congrArg (fun op => op φ ψ) hop

/-- **Math.** The Rayleigh-quotient definition of the curvature-operator norm
scales by `1 / c`: a bound `K` for `c g` is equivalent to the bound `c K` for
`g`. -/
theorem rescaledMetric_hasCurvatureOperatorNormLeAt_iff
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hLC : g.leviCivitaConnection.IsLeviCivita g)
    (hLC' : (rescaledMetric g c hc).leviCivitaConnection.IsLeviCivita
      (rescaledMetric g c hc))
    (p : M) (K : ℝ) :
    HasCurvatureOperatorNormLeAt (rescaledMetric g c hc)
        (rescaledMetric g c hc).leviCivitaConnection hLC' p K ↔
      HasCurvatureOperatorNormLeAt g g.leviCivitaConnection hLC p (c * K) := by
  simp only [HasCurvatureOperatorNormLeAt, HasCurvatureOperatorNormLe]
  constructor
  · intro h φ
    have hφ := h φ
    rw [rescaledMetric_curvatureOperator g c hc hLC hLC' p,
      rescaledMetric_wedgeInner g c hc p, abs_mul, abs_of_pos hc] at hφ
    let A := |(letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
      curvatureOperator (isAlgCurvatureForm_curvatureFormAt
        g g.leviCivitaConnection hLC p) φ φ)|
    let W := (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
      wedgeInner φ φ)
    change c * A ≤ K * (c ^ 2 * W) at hφ
    change A ≤ c * K * W
    have hrhs : K * (c ^ 2 * W) = c * (c * K * W) := by ring
    rw [hrhs] at hφ
    exact le_of_mul_le_mul_left hφ hc
  · intro h φ
    have hφ := h φ
    rw [rescaledMetric_curvatureOperator g c hc hLC hLC' p,
      rescaledMetric_wedgeInner g c hc p, abs_mul, abs_of_pos hc]
    let A := |(letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
      curvatureOperator (isAlgCurvatureForm_curvatureFormAt
        g g.leviCivitaConnection hLC p) φ φ)|
    let W := (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
      wedgeInner φ φ)
    change A ≤ c * K * W at hφ
    change c * A ≤ K * (c ^ 2 * W)
    calc
      c * A ≤ c * (c * K * W) := mul_le_mul_of_nonneg_left hφ hc.le
      _ = K * (c ^ 2 * W) := by ring

/-- **Math.** Direct bound form of `|Rm_{c g}(p)| = |Rm_g(p)| / c`.
Blueprint: `lem:metric-rescaling` (item 2). -/
theorem rescaledMetric_hasCurvatureOperatorNormLeAt_div_iff
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hLC : g.leviCivitaConnection.IsLeviCivita g)
    (hLC' : (rescaledMetric g c hc).leviCivitaConnection.IsLeviCivita
      (rescaledMetric g c hc))
    (p : M) (K : ℝ) :
    HasCurvatureOperatorNormLeAt (rescaledMetric g c hc)
        (rescaledMetric g c hc).leviCivitaConnection hLC' p (K / c) ↔
      HasCurvatureOperatorNormLeAt g g.leviCivitaConnection hLC p K := by
  have h := rescaledMetric_hasCurvatureOperatorNormLeAt_iff
    g c hc hLC hLC' p (K / c)
  have hcancel : c * (K / c) = K := by field_simp
  rwa [hcancel] at h

/-! ### Ricci curvature -/

/-- **Math.** Under `g ↦ c g`, the inverse Riesz identification on a tangent
fibre is multiplied by `c⁻¹`. -/
theorem rescaledMetric_rieszInvEquiv
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) (p : M)
    (f : TangentSpace I p →ₗ[ℝ] ℝ) :
    (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
      Riemannian.rieszInvEquiv (TangentSpace I p) f) =
      c⁻¹ • (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩;
        Riemannian.rieszInvEquiv (TangentSpace I p) f) := by
  let newR : TangentSpace I p :=
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(rescaledMetric g c hc).toRiemannianMetric⟩
    Riemannian.rieszInvEquiv (TangentSpace I p) f
  let oldR : TangentSpace I p :=
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    Riemannian.rieszInvEquiv (TangentSpace I p) f
  change newR = c⁻¹ • oldR
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro z
  have hnew :
      (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
        inner ℝ newR z) = f z := by
    simpa [newR] using
      (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(rescaledMetric g c hc).toRiemannianMetric⟩
       Riemannian.rieszInvEquiv_inner (V := TangentSpace I p) f z)
  have hold : inner ℝ oldR z = f z := by
    simpa [oldR] using
      (Riemannian.rieszInvEquiv_inner (V := TangentSpace I p) f z)
  change (rescaledMetric g c hc).metricInner p newR z = f z at hnew
  rw [rescaledMetric_metricInner] at hnew
  rw [real_inner_smul_left, hold, inv_mul_eq_div]
  change g.metricInner p newR z = f z / c
  apply (eq_div_iff hc.ne').2
  calc
    g.metricInner p newR z * c = c * g.metricInner p newR z := mul_comm _ _
    _ = f z := hnew

/-- **Math.** The bilinear form traced to define Ricci is multiplied by `c`
under `g ↦ c g`. -/
theorem rescaledMetric_ricciBilinAux
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hLC : g.leviCivitaConnection.IsLeviCivita g)
    (hLC' : (rescaledMetric g c hc).leviCivitaConnection.IsLeviCivita
      (rescaledMetric g c hc))
    (p : M) (v w : TangentSpace I p) :
    (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
      Riemannian.ricciBilinAux
        (isAlgCurvatureForm_curvatureFormAt (rescaledMetric g c hc)
          (rescaledMetric g c hc).leviCivitaConnection hLC' p) v w) =
      c • (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩;
        Riemannian.ricciBilinAux
          (isAlgCurvatureForm_curvatureFormAt g g.leviCivitaConnection hLC p) v w) := by
  let newBeta : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(rescaledMetric g c hc).toRiemannianMetric⟩
    Riemannian.ricciBilinAux
      (isAlgCurvatureForm_curvatureFormAt (rescaledMetric g c hc)
        (rescaledMetric g c hc).leviCivitaConnection hLC' p) v w
  let oldBeta : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    Riemannian.ricciBilinAux
      (isAlgCurvatureForm_curvatureFormAt g g.leviCivitaConnection hLC p) v w
  change newBeta = c • oldBeta
  ext z t
  simp only [newBeta, oldBeta, Riemannian.ricciBilinAux,
    LinearMap.smul_apply, smul_eq_mul]
  exact rescaledMetric_curvatureFormAt g c hc p v z w t

/-- **Math.** Ricci curvature as a `(0,2)` tensor is unchanged under constant
positive metric rescaling. -/
theorem rescaledMetric_ricciAt
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hLC : g.leviCivitaConnection.IsLeviCivita g)
    (hLC' : (rescaledMetric g c hc).leviCivitaConnection.IsLeviCivita
      (rescaledMetric g c hc))
    (p : M) (v w : TangentSpace I p) :
    ricciAt (rescaledMetric g c hc)
        (rescaledMetric g c hc).leviCivitaConnection hLC' p v w =
      ricciAt g g.leviCivitaConnection hLC p v w := by
  let newBeta : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(rescaledMetric g c hc).toRiemannianMetric⟩
    Riemannian.ricciBilinAux
      (isAlgCurvatureForm_curvatureFormAt (rescaledMetric g c hc)
        (rescaledMetric g c hc).leviCivitaConnection hLC' p) v w
  let oldBeta : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    Riemannian.ricciBilinAux
      (isAlgCurvatureForm_curvatureFormAt g g.leviCivitaConnection hLC p) v w
  have hbeta : newBeta = c • oldBeta := by
    simpa [newBeta, oldBeta] using
      rescaledMetric_ricciBilinAux g c hc hLC hLC' p v w
  let newEnd : TangentSpace I p →ₗ[ℝ] TangentSpace I p :=
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(rescaledMetric g c hc).toRiemannianMetric⟩
    (Riemannian.rieszInvEquiv (TangentSpace I p)).toLinearMap ∘ₗ newBeta
  let oldEnd : TangentSpace I p →ₗ[ℝ] TangentSpace I p :=
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (Riemannian.rieszInvEquiv (TangentSpace I p)).toLinearMap ∘ₗ oldBeta
  have hend : newEnd = oldEnd := by
    apply LinearMap.ext
    intro z
    simp only [newEnd, oldEnd, LinearMap.comp_apply]
    change (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
      Riemannian.rieszInvEquiv (TangentSpace I p) (newBeta z)) =
      (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩;
        Riemannian.rieszInvEquiv (TangentSpace I p) (oldBeta z))
    rw [rescaledMetric_rieszInvEquiv g c hc p (newBeta z)]
    have hbetaz : newBeta z = c • oldBeta z := by
      rw [hbeta, LinearMap.smul_apply]
    rw [hbetaz]
    change c⁻¹ • (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩;
        Riemannian.rieszInvEquiv (TangentSpace I p) (c • oldBeta z)) =
      (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩;
        Riemannian.rieszInvEquiv (TangentSpace I p) (oldBeta z))
    rw [map_smul]
    simp [hc.ne']
  simp only [ricciAt, Riemannian.ricciForm, Riemannian.bilinTrace]
  change LinearMap.trace ℝ (TangentSpace I p) newEnd =
    LinearMap.trace ℝ (TangentSpace I p) oldEnd
  rw [hend]

/-- **Math.** The pointwise lower bound `Ric ≥ (n-1)k g` is equivalent after
rescaling to `Ric' ≥ (n-1)(k/c) g'`, where `n` is the model dimension.
Blueprint: `lem:metric-rescaling` (item 3). -/
theorem rescaledMetric_ricciLowerBoundAt_iff
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hLC : g.leviCivitaConnection.IsLeviCivita g)
    (hLC' : (rescaledMetric g c hc).leviCivitaConnection.IsLeviCivita
      (rescaledMetric g c hc))
    (p : M) (k : ℝ) :
    (∀ v : TangentSpace I p,
      ((Module.finrank ℝ E : ℝ) - 1) * k * g.metricInner p v v ≤
        ricciAt g g.leviCivitaConnection hLC p v v) ↔
    (∀ v : TangentSpace I p,
      ((Module.finrank ℝ E : ℝ) - 1) * (k / c) *
          (rescaledMetric g c hc).metricInner p v v ≤
        ricciAt (rescaledMetric g c hc)
          (rescaledMetric g c hc).leviCivitaConnection hLC' p v v) := by
  constructor
  · intro h v
    rw [rescaledMetric_ricciAt g c hc hLC hLC' p,
      rescaledMetric_metricInner]
    have hcoeff :
        ((Module.finrank ℝ E : ℝ) - 1) * (k / c) *
            (c * g.metricInner p v v) =
          ((Module.finrank ℝ E : ℝ) - 1) * k * g.metricInner p v v := by
      field_simp
    rw [hcoeff]
    exact h v
  · intro h v
    have hv := h v
    rw [rescaledMetric_ricciAt g c hc hLC hLC' p,
      rescaledMetric_metricInner] at hv
    have hcoeff :
        ((Module.finrank ℝ E : ℝ) - 1) * (k / c) *
            (c * g.metricInner p v v) =
          ((Module.finrank ℝ E : ℝ) - 1) * k * g.metricInner p v v := by
      field_simp
    rwa [hcoeff] at hv

/-! ### Fibre norms and curve speeds -/

/-- **Math.** The tangent-fibre norm is multiplied by `√c` under the
constant rescaling `g ↦ c g`.
This is the pointwise analytic bridge used by the distance and volume clauses
of `lem:metric-rescaling`.
-/
theorem rescaledMetric_norm
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (p : M) (v : TangentSpace I p) :
    (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
      ‖v‖) =
      Real.sqrt c *
        (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨g.toRiemannianMetric⟩;
        ‖v‖) := by
  rw [norm_tangent_eq_sqrt_metricInner, norm_tangent_eq_sqrt_metricInner,
    rescaledMetric_metricInner]
  rw [Real.sqrt_mul (le_of_lt hc)]

/-- **Math.** The extended tangent norm is multiplied by `sqrt c` under
constant positive metric rescaling. -/
theorem rescaledMetric_enorm
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (p : M) (v : TangentSpace I p) :
    (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
      ‖v‖ₑ) =
      ENNReal.ofReal (Real.sqrt c) *
        (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨g.toRiemannianMetric⟩;
          ‖v‖ₑ) := by
  calc
    (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
      ‖v‖ₑ) =
        ENNReal.ofReal (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
          ‖v‖) := by
            exact (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
              ⟨(rescaledMetric g c hc).toRiemannianMetric⟩
              ofReal_norm v).symm
    _ = ENNReal.ofReal (Real.sqrt c *
        (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨g.toRiemannianMetric⟩;
          ‖v‖)) := congrArg ENNReal.ofReal (rescaledMetric_norm g c hc p v)
    _ = ENNReal.ofReal (Real.sqrt c) *
        ENNReal.ofReal (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨g.toRiemannianMetric⟩;
          ‖v‖) := ENNReal.ofReal_mul (Real.sqrt_nonneg c)
    _ = ENNReal.ofReal (Real.sqrt c) *
        (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨g.toRiemannianMetric⟩;
          ‖v‖ₑ) := by
            rw [(letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
              ⟨g.toRiemannianMetric⟩
              ofReal_norm v)]

/-- **Math.** The do Carmo speed of every curve is multiplied by `√c` under
constant metric rescaling.
-/
theorem rescaledMetric_speedSq
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (γ : ℝ → M) (t : ℝ) :
    Riemannian.Geodesic.speedSq (I := I) (rescaledMetric g c hc) γ t =
      c * Riemannian.Geodesic.speedSq (I := I) g γ t := by
  rw [Riemannian.Geodesic.speedSq_def, Riemannian.Geodesic.speedSq_def,
    rescaledMetric_metricInner]

/-- **Math.** The length of a curve for an explicit Riemannian metric,
defined by integrating the square root of its squared speed. -/
noncomputable def metricCurveLength (g : RiemannianMetric I M)
    (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, Real.sqrt (Riemannian.Geodesic.speedSq (I := I) g γ t)

/-- **Math.** Every curve length is multiplied by `sqrt c` under the
constant rescaling `g ↦ c g`. -/
theorem rescaledMetric_curveLength
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (γ : ℝ → M) (a b : ℝ) :
    metricCurveLength (I := I) (rescaledMetric g c hc) γ a b =
      Real.sqrt c * metricCurveLength (I := I) g γ a b := by
  simp only [metricCurveLength, rescaledMetric_speedSq]
  simp_rw [Real.sqrt_mul (le_of_lt hc)]
  rw [intervalIntegral.integral_const_mul]

/-- **Math.** The set of lengths of piecewise differentiable curves from
`p` to `q`, with the metric kept as explicit data. -/
def metricCurveLengthSet (g : RiemannianMetric I M) (p q : M) : Set ℝ :=
  {L | ∃ γ : ℝ → M,
    Riemannian.Geodesic.IsPiecewiseDifferentiableCurve (I := I) γ 0 1 ∧
    γ 0 = p ∧ γ 1 = q ∧ L = metricCurveLength (I := I) g γ 0 1}

/-- **Math.** The Riemannian distance defined as the infimum of lengths of
piecewise differentiable curves joining two points. As usual, points in
different path components receive the junk value `sInf ∅ = 0`. -/
noncomputable def metricInfimumDistance (g : RiemannianMetric I M)
    (p q : M) : ℝ :=
  sInf (metricCurveLengthSet (I := I) g p q)

/-- **Math.** The set of competitor lengths is dilated by `sqrt c` under
constant metric rescaling. -/
theorem rescaledMetric_curveLengthSet
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) (p q : M) :
    metricCurveLengthSet (I := I) (rescaledMetric g c hc) p q =
      Real.sqrt c • metricCurveLengthSet (I := I) g p q := by
  ext L
  constructor
  · rintro ⟨γ, hγ, h0, h1, hL⟩
    refine Set.mem_smul_set.mpr ⟨metricCurveLength (I := I) g γ 0 1,
      ⟨γ, hγ, h0, h1, rfl⟩, ?_⟩
    calc
      Real.sqrt c • metricCurveLength (I := I) g γ 0 1 =
          metricCurveLength (I := I) (rescaledMetric g c hc) γ 0 1 := by
            simpa [smul_eq_mul] using
              (rescaledMetric_curveLength g c hc γ 0 1).symm
      _ = L := hL.symm
  · rintro ⟨L₀, ⟨γ, hγ, h0, h1, hL₀⟩, hscale⟩
    refine ⟨γ, hγ, h0, h1, ?_⟩
    calc
      L = Real.sqrt c • L₀ := hscale.symm
      _ = Real.sqrt c * metricCurveLength (I := I) g γ 0 1 := by
        rw [hL₀]
        rfl
      _ = metricCurveLength (I := I) (rescaledMetric g c hc) γ 0 1 :=
        (rescaledMetric_curveLength g c hc γ 0 1).symm

/-- **Math.** The Riemannian distance defined by the curve-length infimum is
multiplied by `sqrt c` under `g ↦ c g`. -/
theorem rescaledMetric_infimumDistance
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) (p q : M) :
    metricInfimumDistance (I := I) (rescaledMetric g c hc) p q =
      Real.sqrt c * metricInfimumDistance (I := I) g p q := by
  rw [metricInfimumDistance, rescaledMetric_curveLengthSet,
    Real.sInf_smul_of_nonneg (Real.sqrt_nonneg c)]
  rfl

/-- **Math.** The open ball for the explicit infimum distance. -/
def metricInfimumBall (g : RiemannianMetric I M) (p : M) (r : ℝ) : Set M :=
  {q | metricInfimumDistance (I := I) g p q < r}

/-- **Math.** Rescaling both the metric and the radius gives the same open
ball: `B_{c g}(p, sqrt c * r) = B_g(p,r)`. -/
theorem rescaledMetric_infimumBall
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) (p : M) (r : ℝ) :
    metricInfimumBall (I := I) (rescaledMetric g c hc) p (Real.sqrt c * r) =
      metricInfimumBall (I := I) g p r := by
  ext q
  simp only [metricInfimumBall, Set.mem_setOf_eq, rescaledMetric_infimumDistance]
  exact mul_lt_mul_iff_right₀ (Real.sqrt_pos.2 hc)

/-! ### Canonical Riemannian distance -/

/-- **Math.** The path integral used by `Manifold.riemannianEDist` is
multiplied by `sqrt c`. -/
theorem rescaledMetric_pathIntegral
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    {p q : M} (γ : Path p q) :
    (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
      ∫⁻ x, ‖mfderiv% γ x 1‖ₑ) =
      ENNReal.ofReal (Real.sqrt c) *
        (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨g.toRiemannianMetric⟩;
          ∫⁻ x, ‖mfderiv% γ x 1‖ₑ) := by
  let newF : unitInterval → ℝ≥0∞ :=
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(rescaledMetric g c hc).toRiemannianMetric⟩
    fun x => ‖mfderiv% γ x 1‖ₑ
  let oldF : unitInterval → ℝ≥0∞ :=
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    fun x => ‖mfderiv% γ x 1‖ₑ
  change (∫⁻ x, newF x) =
    ENNReal.ofReal (Real.sqrt c) * ∫⁻ x, oldF x
  have hf : ∀ x, newF x = ENNReal.ofReal (Real.sqrt c) * oldF x := by
    intro x
    exact rescaledMetric_enorm g c hc (γ x) (mfderiv% γ x 1)
  simp_rw [hf]
  rw [MeasureTheory.lintegral_const_mul'
    (ENNReal.ofReal (Real.sqrt c)) oldF (by simp)]

/-- **Math.** The canonical Riemannian extended distance is multiplied by
`sqrt c` under `g ↦ c g`. -/
theorem rescaledMetric_riemannianEDist
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) (p q : M) :
    (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
      Manifold.riemannianEDist I p q) =
      ENNReal.ofReal (Real.sqrt c) *
        (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨g.toRiemannianMetric⟩;
          Manifold.riemannianEDist I p q) := by
  rw [Manifold.riemannianEDist, Manifold.riemannianEDist]
  simp_rw [rescaledMetric_pathIntegral g c hc]
  have ha0 : ENNReal.ofReal (Real.sqrt c) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, Real.sqrt_pos.2 hc]
  have hatop : ENNReal.ofReal (Real.sqrt c) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.mul_iInf_of_ne ha0 hatop]
  congr with γ
  rw [ENNReal.mul_iInf_of_ne ha0 hatop]

/-- **Math.** A smooth Riemannian metric supplies the continuity instance required by
the canonical Riemannian metric-space construction. -/
theorem riemannianMetric_isContinuousRiemannianBundle
    (g : RiemannianMetric I M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)
  exact (inferInstance : letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toContinuousRiemannianMetric.toRiemannianMetric⟩
    IsContinuousRiemannianBundle E (TangentSpace I : M → Type _))

/-- **Math.** On a preconnected manifold, the genuine metric induced by
`c g` is `sqrt c` times the metric induced by `g`. -/
theorem rescaledMetric_dist [T3Space M] [PreconnectedSpace M]
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) (p q : M) :
    (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
      letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
        riemannianMetric_isContinuousRiemannianBundle (rescaledMetric g c hc)
      letI : MetricSpace M := MetricSpace.ofRiemannianMetric I M
      dist p q) =
      Real.sqrt c *
        (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨g.toRiemannianMetric⟩;
          letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
            riemannianMetric_isContinuousRiemannianBundle g
          letI : MetricSpace M := MetricSpace.ofRiemannianMetric I M
          dist p q) := by
  change (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
    (Manifold.riemannianEDist I p q).toReal) =
    Real.sqrt c *
      (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩;
        (Manifold.riemannianEDist I p q).toReal)
  rw [rescaledMetric_riemannianEDist g c hc p q, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg c)]

/-- **Math.** Rescaling the canonical Riemannian metric and the radius gives
the same open ball. -/
theorem rescaledMetric_ball [T3Space M] [PreconnectedSpace M]
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) (p : M) (r : ℝ) :
    (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
      letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
        riemannianMetric_isContinuousRiemannianBundle (rescaledMetric g c hc)
      letI : MetricSpace M := MetricSpace.ofRiemannianMetric I M
      Metric.ball p (Real.sqrt c * r)) =
      (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
          riemannianMetric_isContinuousRiemannianBundle g
        letI : MetricSpace M := MetricSpace.ofRiemannianMetric I M
        Metric.ball p r) := by
  ext q
  change (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      riemannianMetric_isContinuousRiemannianBundle (rescaledMetric g c hc)
    letI : MetricSpace M := MetricSpace.ofRiemannianMetric I M
    dist q p < Real.sqrt c * r) ↔
    (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩;
      letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
        riemannianMetric_isContinuousRiemannianBundle g
      letI : MetricSpace M := MetricSpace.ofRiemannianMetric I M
      dist q p < r)
  rw [rescaledMetric_dist g c hc]
  exact mul_lt_mul_iff_right₀ (Real.sqrt_pos.2 hc)

/-- **Math.** Completeness is unchanged by a positive constant rescaling of
the canonical Riemannian metric. Blueprint: `lem:metric-rescaling` (item 4). -/
theorem rescaledMetric_completeSpace_iff [T3Space M] [PreconnectedSpace M]
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) :
    (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
      letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
        riemannianMetric_isContinuousRiemannianBundle (rescaledMetric g c hc)
      letI : MetricSpace M := MetricSpace.ofRiemannianMetric I M
      CompleteSpace M) ↔
      (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
          riemannianMetric_isContinuousRiemannianBundle g
        letI : MetricSpace M := MetricSpace.ofRiemannianMetric I M
        CompleteSpace M) := by
  let newMetric : MetricSpace M :=
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(rescaledMetric g c hc).toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      riemannianMetric_isContinuousRiemannianBundle (rescaledMetric g c hc)
    MetricSpace.ofRiemannianMetric I M
  let oldMetric : MetricSpace M :=
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      riemannianMetric_isContinuousRiemannianBundle g
    MetricSpace.ofRiemannianMetric I M
  have hdist : ∀ p q : M,
      @dist M newMetric.toDist p q =
        Real.sqrt c * @dist M oldMetric.toDist p q := by
    intro p q
    simpa [newMetric, oldMetric] using rescaledMetric_dist g c hc p q
  have hforward :
      @UniformContinuous M M oldMetric.toUniformSpace newMetric.toUniformSpace id := by
    rw [@Metric.uniformContinuous_iff M M oldMetric.toPseudoMetricSpace
      newMetric.toPseudoMetricSpace id]
    intro ε hε
    refine ⟨ε / Real.sqrt c, div_pos hε (Real.sqrt_pos.2 hc), ?_⟩
    intro p q hpq
    change @dist M newMetric.toDist p q < ε
    rw [hdist]
    calc
      Real.sqrt c * @dist M oldMetric.toDist p q <
          Real.sqrt c * (ε / Real.sqrt c) :=
        mul_lt_mul_of_pos_left hpq (Real.sqrt_pos.2 hc)
      _ = ε := by field_simp
  have hbackward :
      @UniformContinuous M M newMetric.toUniformSpace oldMetric.toUniformSpace id := by
    rw [@Metric.uniformContinuous_iff M M newMetric.toPseudoMetricSpace
      oldMetric.toPseudoMetricSpace id]
    intro ε hε
    refine ⟨Real.sqrt c * ε, mul_pos (Real.sqrt_pos.2 hc) hε, ?_⟩
    intro p q hpq
    change @dist M oldMetric.toDist p q < ε
    have hmul : Real.sqrt c * @dist M oldMetric.toDist p q <
        Real.sqrt c * ε := by
      rw [← hdist]
      exact hpq
    exact lt_of_mul_lt_mul_left hmul (Real.sqrt_nonneg c)
  let e : @UniformEquiv M M oldMetric.toUniformSpace newMetric.toUniformSpace :=
    @UniformEquiv.mk M M oldMetric.toUniformSpace newMetric.toUniformSpace
      (Equiv.refl M) hforward hbackward
  change @CompleteSpace M newMetric.toUniformSpace ↔
    @CompleteSpace M oldMetric.toUniformSpace
  exact (@UniformEquiv.completeSpace_iff M M oldMetric.toUniformSpace
    newMetric.toUniformSpace e).symm

/-! ### Riemannian volume density -/

/-- **Math.** Every chart Gram matrix is multiplied by `c` under constant
metric rescaling. -/
theorem rescaledMetric_chartGramMatrix
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) (α x : M) :
    Riemannian.Tensor.chartGramMatrix (I := I) (rescaledMetric g c hc) α x =
      c • Riemannian.Tensor.chartGramMatrix (I := I) g α x := by
  ext i j
  rfl

/-- **Math.** Every chart Gram entry is multiplied by `c` under constant
metric rescaling. -/
theorem rescaledMetric_chartGramOnE
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (α : M) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramOnE (I := I) (rescaledMetric g c hc) α i j y =
      c * chartGramOnE (I := I) g α i j y := by
  have h := congrArg (fun A : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ => A i j)
    (rescaledMetric_chartGramMatrix g c hc α ((extChartAt I α).symm y))
  simpa only [chartGramOnE_def, Matrix.smul_apply, smul_eq_mul] using h

/-- **Math.** On a chart base set, the inverse Gram matrix is multiplied by
`c⁻¹` under constant metric rescaling. -/
theorem rescaledMetric_chartInvGramMatrix
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (α x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    Riemannian.Tensor.chartInvGramMatrix (I := I) (rescaledMetric g c hc) α x =
      c⁻¹ • Riemannian.Tensor.chartInvGramMatrix (I := I) g α x := by
  letI : Invertible c := invertibleOfNonzero hc.ne'
  unfold Riemannian.Tensor.chartInvGramMatrix
  rw [rescaledMetric_chartGramMatrix]
  rw [Matrix.inv_smul]
  · change ⅟c • (Riemannian.Tensor.chartGramMatrix (I := I) g α x)⁻¹ =
      c⁻¹ • (Riemannian.Tensor.chartGramMatrix (I := I) g α x)⁻¹
    congr
  · exact isUnit_iff_ne_zero.mpr
      (ne_of_gt (Riemannian.Tensor.chartGramMatrix_posDef
        (I := I) g α hx).det_pos)

/-- **Math.** Coordinate derivatives of chart Gram entries are multiplied by
`c` under constant metric rescaling. -/
theorem rescaledMetric_partialDeriv_chartGramOnE
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (α : M) (i j k : Fin (Module.finrank ℝ E)) (y : E)
    (hy : y ∈ (extChartAt I α).target) :
    partialDeriv (E := E) k
        (chartGramOnE (I := I) (rescaledMetric g c hc) α i j) y =
      c * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y := by
  have hfun : chartGramOnE (I := I) (rescaledMetric g c hc) α i j =
      fun z => c * chartGramOnE (I := I) g α i j z := by
    funext z
    exact rescaledMetric_chartGramOnE g c hc α i j z
  rw [hfun]
  unfold partialDeriv
  rw [fderiv_const_mul]
  · simp
  · exact ((chartGramOnE_contDiffOn (I := I) g α i j).differentiableOn
      (by norm_num)).differentiableAt
        ((isOpen_extChartAt_target (I := I) α).mem_nhds hy)

/-- **Math.** Constant metric rescaling leaves every coordinate Christoffel
symbol unchanged on its chart target. -/
theorem rescaledMetric_chartChristoffel
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (α : M) (i j k : Fin (Module.finrank ℝ E)) (y : E)
    (hy : y ∈ (extChartAt I α).target) :
    chartChristoffel (I := I) (rescaledMetric g c hc) α i j k y =
      chartChristoffel (I := I) g α i j k y := by
  classical
  have hbase : (extChartAt I α).symm y ∈
      (trivializationAt E (TangentSpace I) α).baseSet := by
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  rw [chartChristoffel_def, chartChristoffel_def]
  have hinv := rescaledMetric_chartInvGramMatrix g c hc α
    ((extChartAt I α).symm y) hbase
  have hderiv : ∀ a b d, partialDeriv (E := E) d
        (chartGramOnE (I := I) (rescaledMetric g c hc) α a b) y =
      c * partialDeriv (E := E) d (chartGramOnE (I := I) g α a b) y :=
    fun a b d => rescaledMetric_partialDeriv_chartGramOnE
      g c hc α a b d y hy
  simp only [hinv, Matrix.smul_apply, smul_eq_mul, hderiv]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro l _
  field_simp

/-- **Math.** Constant metric rescaling leaves the coordinate Christoffel
contraction unchanged on its chart target. -/
theorem rescaledMetric_chartChristoffelContraction
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (α : M) (v w y : E) (hy : y ∈ (extChartAt I α).target) :
    Riemannian.Geodesic.chartChristoffelContraction
        (I := I) (rescaledMetric g c hc) α v w y =
      Riemannian.Geodesic.chartChristoffelContraction (I := I) g α v w y := by
  classical
  simp only [Riemannian.Geodesic.chartChristoffelContraction_def]
  simp_rw [rescaledMetric_chartChristoffel g c hc α _ _ _ y hy]

/-- **Math.** A parameterized curve satisfies the geodesic equation at a time
for `c g` if and only if it does so for `g`. -/
theorem rescaledMetric_hasGeodesicEquationAt_iff
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (γ : ℝ → M) (t : ℝ) :
    Riemannian.Geodesic.HasGeodesicEquationAt
        (I := I) (rescaledMetric g c hc) γ t ↔
      Riemannian.Geodesic.HasGeodesicEquationAt (I := I) g γ t := by
  have hsource : γ t ∈ (extChartAt I (γ t)).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H (γ t)
  have hy : extChartAt I (γ t) (γ t) ∈ (extChartAt I (γ t)).target :=
    (extChartAt I (γ t)).map_source hsource
  unfold Riemannian.Geodesic.HasGeodesicEquationAt
  constructor
  · rintro ⟨v, a, hv, hdv, ha, heq⟩
    refine ⟨v, a, hv, hdv, ha, ?_⟩
    rwa [rescaledMetric_chartChristoffelContraction g c hc (γ t) v v _ hy] at heq
  · rintro ⟨v, a, hv, hdv, ha, heq⟩
    refine ⟨v, a, hv, hdv, ha, ?_⟩
    rwa [rescaledMetric_chartChristoffelContraction g c hc (γ t) v v _ hy]

/-- **Math.** Constant metric rescaling preserves parameterized geodesics on
every set of times. -/
theorem rescaledMetric_isGeodesicOn_iff
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (γ : ℝ → M) (s : Set ℝ) :
    Riemannian.Geodesic.IsGeodesicOn (I := I) (rescaledMetric g c hc) γ s ↔
      Riemannian.Geodesic.IsGeodesicOn (I := I) g γ s := by
  constructor
  · intro h t ht
    exact (rescaledMetric_hasGeodesicEquationAt_iff g c hc γ t).mp (h t ht)
  · intro h t ht
    exact (rescaledMetric_hasGeodesicEquationAt_iff g c hc γ t).mpr (h t ht)

/-- **Math.** Constant metric rescaling preserves global parameterized
geodesics. -/
theorem rescaledMetric_isGeodesic_iff
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) (γ : ℝ → M) :
    Riemannian.Geodesic.IsGeodesic (I := I) (rescaledMetric g c hc) γ ↔
      Riemannian.Geodesic.IsGeodesic (I := I) g γ := by
  constructor
  · intro h t
    exact (rescaledMetric_hasGeodesicEquationAt_iff g c hc γ t).mp (h t)
  · intro h t
    exact (rescaledMetric_hasGeodesicEquationAt_iff g c hc γ t).mpr (h t)

/-! ### Intrinsic exponential maps -/

section IntrinsicExponential

variable {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [SigmaCompactSpace N] [T2Space N]

/-- **Math.** Constant metric rescaling preserves continuous intrinsic geodesics
with prescribed initial data on every parameter domain. -/
theorem rescaledMetric_isIntrinsicGeodesicOnWithInitial_iff
    (g : RiemannianMetric I N) (c : ℝ) (hc : 0 < c)
    (γ : ℝ → N) (s : Set ℝ) (p : N) (v : TangentSpace I p) :
    Riemannian.Geodesic.IsIntrinsicGeodesicOnWithInitial
        (I := I) (rescaledMetric g c hc) γ s p v ↔
      Riemannian.Geodesic.IsIntrinsicGeodesicOnWithInitial (I := I) g γ s p v := by
  constructor
  · rintro ⟨h0, hv, hcont, hgeo⟩
    exact ⟨h0, hv, hcont,
      (rescaledMetric_isGeodesicOn_iff g c hc γ s).mp hgeo⟩
  · rintro ⟨h0, hv, hcont, hgeo⟩
    exact ⟨h0, hv, hcont,
      (rescaledMetric_isGeodesicOn_iff g c hc γ s).mpr hgeo⟩

/-- **Math.** A time belongs to the intrinsic maximal geodesic interval for
`c g` if and only if it belongs to the interval for `g`. -/
theorem rescaledMetric_intrinsicGeodesicWitness_iff
    (g : RiemannianMetric I N) (c : ℝ) (hc : 0 < c)
    (p : N) (v : TangentSpace I p) (t : ℝ) :
    Riemannian.Geodesic.IntrinsicGeodesicWitness
        (I := I) (rescaledMetric g c hc) p v t ↔
      Riemannian.Geodesic.IntrinsicGeodesicWitness (I := I) g p v t := by
  constructor
  · rintro ⟨γ, J, hJ, hJconn, h0J, htJ, hγ⟩
    exact ⟨γ, J, hJ, hJconn, h0J, htJ,
      (rescaledMetric_isIntrinsicGeodesicOnWithInitial_iff
        g c hc γ J p v).mp hγ⟩
  · rintro ⟨γ, J, hJ, hJconn, h0J, htJ, hγ⟩
    exact ⟨γ, J, hJ, hJconn, h0J, htJ,
      (rescaledMetric_isIntrinsicGeodesicOnWithInitial_iff
        g c hc γ J p v).mpr hγ⟩

/-- **Math.** Constant metric rescaling leaves the intrinsic maximal interval
of every geodesic unchanged. -/
theorem rescaledMetric_intrinsicGeodesicInterval
    (g : RiemannianMetric I N) (c : ℝ) (hc : 0 < c)
    (p : N) (v : TangentSpace I p) :
    Riemannian.Geodesic.intrinsicGeodesicInterval
        (I := I) (rescaledMetric g c hc) p v =
      Riemannian.Geodesic.intrinsicGeodesicInterval (I := I) g p v := by
  ext t
  exact rescaledMetric_intrinsicGeodesicWitness_iff g c hc p v t

/-- **Math.** Constant metric rescaling leaves the natural domain of the
intrinsic exponential map unchanged. -/
theorem rescaledMetric_expDomainIntrinsic
    (g : RiemannianMetric I N) (c : ℝ) (hc : 0 < c) (p : N) :
    Riemannian.Exponential.expDomainIntrinsic
        (I := I) (rescaledMetric g c hc) p =
      Riemannian.Exponential.expDomainIntrinsic (I := I) g p := by
  ext v
  exact rescaledMetric_intrinsicGeodesicWitness_iff g c hc p v 1

/-- **Math.** Constant metric rescaling leaves the genuine intrinsic
exponential map unchanged, including its conventional value outside the
natural domain. Blueprint: `lem:metric-rescaling` (item 1). -/
theorem rescaledMetric_expMapIntrinsic
    (g : RiemannianMetric I N) (c : ℝ) (hc : 0 < c)
    (p : N) (v : TangentSpace I p) :
    Riemannian.Exponential.expMapIntrinsic
        (I := I) (rescaledMetric g c hc) p v =
      Riemannian.Exponential.expMapIntrinsic (I := I) g p v := by
  by_cases hv : v ∈ Riemannian.Exponential.expDomainIntrinsic (I := I) g p
  · obtain ⟨γ, J, hJ, hJconn, h0J, h1J, hγ⟩ := hv
    have hγ' := (rescaledMetric_isIntrinsicGeodesicOnWithInitial_iff
      g c hc γ J p v).mpr hγ
    rw [Riemannian.Exponential.expMapIntrinsic_eq_of_witness
        (rescaledMetric g c hc) hJ hJconn h0J h1J hγ',
      Riemannian.Exponential.expMapIntrinsic_eq_of_witness
        g hJ hJconn h0J h1J hγ]
  · have hv' : v ∉ Riemannian.Exponential.expDomainIntrinsic
        (I := I) (rescaledMetric g c hc) p := by
      rwa [rescaledMetric_expDomainIntrinsic g c hc p]
    change ¬ Riemannian.Geodesic.IntrinsicGeodesicWitness
      (I := I) g p v 1 at hv
    change ¬ Riemannian.Geodesic.IntrinsicGeodesicWitness
      (I := I) (rescaledMetric g c hc) p v 1 at hv'
    change Riemannian.Geodesic.intrinsicMaximalGeodesic
        (I := I) (rescaledMetric g c hc) p v 1 =
      Riemannian.Geodesic.intrinsicMaximalGeodesic (I := I) g p v 1
    rw [Riemannian.Geodesic.intrinsicMaximalGeodesic, dif_neg hv',
      Riemannian.Geodesic.intrinsicMaximalGeodesic, dif_neg hv]

end IntrinsicExponential

/-- **Math.** In every chart, the Riemannian volume density is multiplied by
`sqrt (c^n)`, where `n` is the manifold dimension. -/
theorem rescaledMetric_chartVolumeDensity
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) (α : M) (y : E) :
    chartVolumeDensity (I := I) (rescaledMetric g c hc) α y =
      Real.sqrt (c ^ Module.finrank ℝ E) *
        chartVolumeDensity (I := I) g α y := by
  unfold chartVolumeDensity
  rw [rescaledMetric_chartGramMatrix, Matrix.det_smul]
  simp only [Fintype.card_fin]
  rw [Real.sqrt_mul (pow_nonneg (le_of_lt hc) _)]

/-- **Math.** Each chart measure is multiplied by `sqrt (c^n)` under
constant metric rescaling. -/
theorem rescaledMetric_chartMeasure
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) (α : M) :
    chartMeasure (I := I) (rescaledMetric g c hc) μ α =
      ENNReal.ofReal (Real.sqrt (c ^ Module.finrank ℝ E)) •
        chartMeasure (I := I) g μ α := by
  ext s hs
  rw [MeasureTheory.Measure.smul_apply, chartMeasure_apply μ _ α hs,
    chartMeasure_apply μ _ α hs]
  simp only [smul_eq_mul, rescaledMetric_chartVolumeDensity,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]

/-- **Math.** The global Riemannian measure is multiplied by `sqrt (c^n)`
under constant metric rescaling. -/
theorem rescaledMetric_riemannianMeasure
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
    [SecondCountableTopology M] [Nonempty M]
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) :
    riemannianMeasure (I := I) (rescaledMetric g c hc) μ =
      ENNReal.ofReal (Real.sqrt (c ^ Module.finrank ℝ E)) •
        riemannianMeasure (I := I) g μ := by
  ext s hs
  rw [MeasureTheory.Measure.smul_apply]
  simp only [smul_eq_mul, riemannianMeasure,
    MeasureTheory.Measure.sum_apply _ hs,
    MeasureTheory.Measure.restrict_apply hs]
  have hscale : ∀ n : ℕ,
      chartMeasure (I := I) (rescaledMetric g c hc) μ
          (chartCover (I := I) (M := M) n)
          (s ∩ chartPiece (I := I) (M := M) n) =
        ENNReal.ofReal (Real.sqrt (c ^ Module.finrank ℝ E)) *
          chartMeasure (I := I) g μ (chartCover (I := I) (M := M) n)
            (s ∩ chartPiece (I := I) (M := M) n) := by
    intro n
    have h := congrArg
      (fun ν : MeasureTheory.Measure M =>
        ν (s ∩ chartPiece (I := I) (M := M) n))
      (rescaledMetric_chartMeasure μ g c hc
        (chartCover (I := I) (M := M) n))
    simpa only [MeasureTheory.Measure.smul_apply, smul_eq_mul] using h
  simp_rw [hscale]
  exact ENNReal.tsum_mul_left

/-- **Math.** For `c > 0`, the determinant-density factor `sqrt (c^n)` is
the usual real power `c^(n/2)`. -/
theorem sqrt_pow_eq_rpow_half (c : ℝ) (hc : 0 < c) (n : ℕ) :
    Real.sqrt (c ^ n) = c ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hc.le]
  congr 1
  ring

/-- **Math.** Chart volume densities scale by `c^(n/2)`, in the exponent
normalization used in the blueprint. -/
theorem rescaledMetric_chartVolumeDensity_rpow
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) (α : M) (y : E) :
    chartVolumeDensity (I := I) (rescaledMetric g c hc) α y =
      c ^ ((Module.finrank ℝ E : ℝ) / 2) * chartVolumeDensity (I := I) g α y := by
  rw [rescaledMetric_chartVolumeDensity, sqrt_pow_eq_rpow_half c hc]

/-- **Math.** Each chart measure scales by `c^(n/2)`. -/
theorem rescaledMetric_chartMeasure_rpow
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) (α : M) :
    chartMeasure (I := I) (rescaledMetric g c hc) μ α =
      ENNReal.ofReal (c ^ ((Module.finrank ℝ E : ℝ) / 2)) •
        chartMeasure (I := I) g μ α := by
  rw [rescaledMetric_chartMeasure, sqrt_pow_eq_rpow_half c hc]

/-- **Math.** The global Riemannian volume measure scales by `c^(n/2)`.
Blueprint: `lem:metric-rescaling` (item 5). -/
theorem rescaledMetric_riemannianMeasure_rpow
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
    [SecondCountableTopology M] [Nonempty M]
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) :
    riemannianMeasure (I := I) (rescaledMetric g c hc) μ =
      ENNReal.ofReal (c ^ ((Module.finrank ℝ E : ℝ) / 2)) •
        riemannianMeasure (I := I) g μ := by
  rw [rescaledMetric_riemannianMeasure, sqrt_pow_eq_rpow_half c hc]

/-- **Math.** Every sectional curvature is divided by `c` under the constant
rescaling `g ↦ c g`.
Blueprint: `lem:metric-rescaling` (item 2). -/
theorem rescaledMetric_sectionalCurvatureAt
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (p : M) (v w : TangentSpace I p) :
    sectionalCurvatureAt (rescaledMetric g c hc)
        (rescaledMetric g c hc).leviCivitaConnection p v w =
      sectionalCurvatureAt g g.leviCivitaConnection p v w / c := by
  change (curvatureFormAt (rescaledMetric g c hc)
      (rescaledMetric g c hc).leviCivitaConnection p v w v w /
        (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨(rescaledMetric g c hc).toRiemannianMetric⟩;
        Riemannian.wedgeSq v w)) =
    (curvatureFormAt g g.leviCivitaConnection p v w v w /
      (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩;
      Riemannian.wedgeSq v w)) / c
  rw [rescaledMetric_curvatureFormAt, rescaledMetric_wedgeSq]
  field_simp

end MorganTianLib
