import MorganTianLib.Ch01.RiemannianCone
import MorganTianLib.Ch01.PointwiseCurvature

/-!
# Morgan--Tian Ch. 1 -- curvature of the Riemannian cone

This module completes the geometric curvature calculation begun in
`RiemannianCone`.  The connection convention below is DoCarmoLib's; after
lowering an index, its curvature form is Morgan--Tian's curvature form.
-/

open Set Riemannian TopologicalSpace
open exteriorPower
open scoped Manifold Topology ContDiff Bundle

noncomputable section

namespace MorganTianLib

section ConeCurvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ N]
    [I.Boundaryless] [SigmaCompactSpace N] [T2Space N] in
@[simp] theorem coneTangent_add (x : N) (r : ↥positiveReal)
    (u v : TangentSpace I x) (a b : ℝ) :
    ((u, a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) +
        ((v, b) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) =
      ((u + v, a + b) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) := by
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ N]
    [I.Boundaryless] [SigmaCompactSpace N] [T2Space N] in
@[simp] theorem coneTangent_sub (x : N) (r : ↥positiveReal)
    (u v : TangentSpace I x) (a b : ℝ) :
    ((u, a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) -
        ((v, b) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) =
      ((u - v, a - b) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) := by
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ N]
    [I.Boundaryless] [SigmaCompactSpace N] [T2Space N] in
@[simp] theorem coneTangent_smul (x : N) (r : ↥positiveReal)
    (c : ℝ) (u : TangentSpace I x) (a : ℝ) :
    c • ((u, a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) =
      ((c • u, c • a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) := by
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ N]
    [I.Boundaryless] [SigmaCompactSpace N] [T2Space N] in
theorem coneTangent_ext (x : N) (r : ↥positiveReal)
    {u v : TangentSpace I x} {a b : ℝ} (hu : u = v) (ha : a = b) :
    ((u, a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) =
      ((v, b) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) := by
  subst v
  subst b
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ N]
    [I.Boundaryless] [SigmaCompactSpace N] [T2Space N] in
@[simp] theorem coneTangent_fst (x : N) (r : ↥positiveReal)
    (u : TangentSpace I x) (a : ℝ) :
    (((u, a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r))).1 = u := by
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ N]
    [I.Boundaryless] [SigmaCompactSpace N] [T2Space N] in
@[simp] theorem coneTangent_snd (x : N) (r : ↥positiveReal)
    (u : TangentSpace I x) (a : ℝ) :
    (((u, a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r))).2 = a := by
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
    [SigmaCompactSpace N] [T2Space N] in
/-- **Math.** A horizontal lift annihilates the reciprocal cone radius. -/
@[simp] theorem coneHorizontalLift_dir_invRadius (X : SmoothVectorField I N)
    (q : N × ↥positiveReal) :
    (coneHorizontalLift X).dir
        (fun p => (coneRadius (N := N) p)⁻¹) q = 0 := by
  rw [coneHorizontalLift_dir X coneInvRadius_contMDiff q]
  change X.dir (fun _ : N => ((q.2 : ℝ)⁻¹)) q.1 = 0
  rw [SmoothVectorField.dir, mfderiv_const]
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
    [SigmaCompactSpace N] [T2Space N] in
/-- **Math.** The horizontal derivative of the scalar multiplying the radial correction. -/
theorem coneHorizontalLift_dir_radialCorrectionScalar
    (g : RiemannianMetric I N) (A X Z : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    (coneHorizontalLift A).dir
        (fun q => -(coneRadius (N := N) q *
          g.metricInner q.1 (X q.1) (Z q.1))) (x, r) =
      -(r : ℝ) * A.dir (fun p => g.metricInner p (X p) (Z p)) x := by
  have hf : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : N × ↥positiveReal => -(coneRadius (N := N) q *
        g.metricInner q.1 (X q.1) (Z q.1))) := by
    simpa only [Pi.mul_apply, Pi.neg_apply] using
      (coneRadius_contMDiff.mul (coneBaseMetricPairing_contMDiff g X Z)).neg
  rw [coneHorizontalLift_dir A hf (x, r)]
  change A.dir (fun y : N => -((r : ℝ) * g.metricInner y (X y) (Z y))) x = _
  have hfun :
      (fun y : N => -((r : ℝ) * g.metricInner y (X y) (Z y))) =
        fun y => (-(r : ℝ)) * g.metricInner y (X y) (Z y) := by
    funext y
    ring
  rw [hfun, A.dir_const_mul (-(r : ℝ)) x
    (g.metricInner_field_mdifferentiableAt X Z x)]

/-- **Math.** Differentiating a radial correction horizontally produces its horizontal
Weingarten term and the derivative of its scalar coefficient. -/
theorem coneLeviCivitaConnection_cov_horizontal_radialCorrection_apply
    (g : RiemannianMetric I N) (A X Z : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    ((coneLeviCivitaConnection g).cov (coneHorizontalLift A)
      (coneRadialCorrection g X Z)) (x, r) =
      (-(g.metricInner x (X x) (Z x)) • A x,
        -(r : ℝ) * A.dir (fun p => g.metricInner p (X p) (Z p)) x) := by
  unfold coneRadialCorrection
  rw [(coneLeviCivitaConnection g).leibniz,
    coneLeviCivitaConnection_cov_horizontal_radial]
  simp only [coneInvRadiusHorizontal_apply, coneRadialField_apply]
  rw [coneHorizontalLift_dir_radialCorrectionScalar]
  simp only [coneRadius]
  have hcoeff :
      (-((r : ℝ) * g.metricInner x (X x) (Z x))) * (r : ℝ)⁻¹ =
        -(g.metricInner x (X x) (Z x)) := by
    field_simp [ne_of_gt (positiveReal_mem r)]
  calc
    _ = (((-((r : ℝ) * g.metricInner x (X x) (Z x))) •
            ((r : ℝ)⁻¹ • A x),
          (-((r : ℝ) * g.metricInner x (X x) (Z x))) • (0 : ℝ)) :
          TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) +
        (((-(r : ℝ) * A.dir (fun p => g.metricInner p (X p) (Z p)) x) •
            (0 : TangentSpace I x),
          (-(r : ℝ) * A.dir (fun p => g.metricInner p (X p) (Z p)) x) •
            (1 : ℝ)) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) :=
      congrArg₂
        (fun u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r) => u + v)
        (coneTangent_smul (I := I) x r
          (-((r : ℝ) * g.metricInner x (X x) (Z x)))
          ((r : ℝ)⁻¹ • A x) 0)
        (coneTangent_smul (I := I) x r
          (-(r : ℝ) * A.dir (fun p => g.metricInner p (X p) (Z p)) x)
          0 1)
    _ = (((-((r : ℝ) * g.metricInner x (X x) (Z x))) •
              ((r : ℝ)⁻¹ • A x) +
            (-(r : ℝ) * A.dir (fun p => g.metricInner p (X p) (Z p)) x) •
              (0 : TangentSpace I x),
          (-((r : ℝ) * g.metricInner x (X x) (Z x))) • (0 : ℝ) +
            (-(r : ℝ) * A.dir (fun p => g.metricInner p (X p) (Z p)) x) • 1) :
          TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) :=
      coneTangent_add (I := I) x r
        ((-((r : ℝ) * g.metricInner x (X x) (Z x))) •
          ((r : ℝ)⁻¹ • A x))
        ((-(r : ℝ) * A.dir (fun p => g.metricInner p (X p) (Z p)) x) •
          (0 : TangentSpace I x))
        ((-((r : ℝ) * g.metricInner x (X x) (Z x))) • (0 : ℝ))
        ((-(r : ℝ) * A.dir (fun p => g.metricInner p (X p) (Z p)) x) •
          (1 : ℝ))
    _ = _ := by
      apply coneTangent_ext (I := I) x r
      · rw [smul_smul, hcoeff]
        module
      · simp

/-- **Math.** The horizontal part of the cone curvature is the base curvature minus the
constant-curvature-one correction.  This uses DoCarmoLib's `(1,3)` sign
convention; lowering the output gives `R_g - g wedge g`. -/
theorem coneCurvature_horizontal_horizontal_horizontal_apply
    (g : RiemannianMetric I N) (X Y Z : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    ((coneLeviCivitaConnection g).curvature (coneHorizontalLift X)
      (coneHorizontalLift Y) (coneHorizontalLift Z)) (x, r) =
      (((leviCivitaConnectionGeneral g).curvature X Y Z) x
          - g.metricInner x (X x) (Z x) • Y x
          + g.metricInner x (Y x) (Z x) • X x,
        0) := by
  let aH : TangentSpace I x :=
    ((leviCivitaConnectionGeneral g).cov Y
      ((leviCivitaConnectionGeneral g).cov X Z)) x +
      -(g.metricInner x (X x) (Z x)) • Y x
  let aR : ℝ :=
    (-(r : ℝ) * g.metricInner x (Y x)
      (((leviCivitaConnectionGeneral g).cov X Z) x)) +
      (-(r : ℝ) * Y.dir (fun p => g.metricInner p (X p) (Z p)) x)
  let bH : TangentSpace I x :=
    ((leviCivitaConnectionGeneral g).cov X
      ((leviCivitaConnectionGeneral g).cov Y Z)) x +
      -(g.metricInner x (Y x) (Z x)) • X x
  let bR : ℝ :=
    (-(r : ℝ) * g.metricInner x (X x)
      (((leviCivitaConnectionGeneral g).cov Y Z) x)) +
      (-(r : ℝ) * X.dir (fun p => g.metricInner p (Y p) (Z p)) x)
  let cH : TangentSpace I x :=
    ((leviCivitaConnectionGeneral g).cov (bracketField X Y) Z) x
  let cR : ℝ :=
    -(r : ℝ) * g.metricInner x ((bracketField X Y) x) (Z x)
  let aT : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r) := (aH, aR)
  let bT : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r) := (bH, bR)
  let cT : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r) := (cH, cR)
  let dT : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r) :=
    (aH - bH, aR - bR)
  let outT : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r) :=
    (aH - bH + cH, aR - bR + cR)
  have hA :
      ((coneLeviCivitaConnection g).cov (coneHorizontalLift Y)
        ((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
          (coneHorizontalLift Z))) (x, r) = aT := by
    have hAraw :
        ((coneLeviCivitaConnection g).cov (coneHorizontalLift Y)
          ((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
            (coneHorizontalLift Z))) (x, r) =
          ((((leviCivitaConnectionGeneral g).cov Y
                ((leviCivitaConnectionGeneral g).cov X Z)) x,
              -(r : ℝ) * g.metricInner x (Y x)
                (((leviCivitaConnectionGeneral g).cov X Z) x)) :
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) +
          ((-(g.metricInner x (X x) (Z x)) • Y x,
              -(r : ℝ) *
                Y.dir (fun p => g.metricInner p (X p) (Z p)) x) :
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) := by
      calc
        _ = ((coneLeviCivitaConnection g).cov (coneHorizontalLift Y)
            (coneHorizontalLift ((leviCivitaConnectionGeneral g).cov X Z) +
              coneRadialCorrection g X Z)) (x, r) :=
          congrArg
            (fun V => ((coneLeviCivitaConnection g).cov
              (coneHorizontalLift Y) V) (x, r))
            (coneLeviCivitaConnection_cov_horizontal_horizontal g X Z)
        _ = (((coneLeviCivitaConnection g).cov (coneHorizontalLift Y)
              (coneHorizontalLift ((leviCivitaConnectionGeneral g).cov X Z))) +
            ((coneLeviCivitaConnection g).cov (coneHorizontalLift Y)
              (coneRadialCorrection g X Z))) (x, r) :=
          congrArg (fun V => V (x, r))
            ((coneLeviCivitaConnection g).add_right (coneHorizontalLift Y)
              (coneHorizontalLift ((leviCivitaConnectionGeneral g).cov X Z))
              (coneRadialCorrection g X Z))
        _ = ((((leviCivitaConnectionGeneral g).cov Y
                ((leviCivitaConnectionGeneral g).cov X Z)) x,
              -(r : ℝ) * g.metricInner x (Y x)
                (((leviCivitaConnectionGeneral g).cov X Z) x)) :
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) +
          ((-(g.metricInner x (X x) (Z x)) • Y x,
              -(r : ℝ) *
                Y.dir (fun p => g.metricInner p (X p) (Z p)) x) :
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) := by
          rw [SmoothVectorField.add_apply,
            coneLeviCivitaConnection_cov_horizontal_horizontal_apply,
            coneLeviCivitaConnection_cov_horizontal_radialCorrection_apply] <;>
            with_unfolding_all rfl
    have hAadd :
        ((((leviCivitaConnectionGeneral g).cov Y
              ((leviCivitaConnectionGeneral g).cov X Z)) x,
            -(r : ℝ) * g.metricInner x (Y x)
              (((leviCivitaConnectionGeneral g).cov X Z) x)) :
          TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) +
        ((-(g.metricInner x (X x) (Z x)) • Y x,
            -(r : ℝ) * Y.dir (fun p => g.metricInner p (X p) (Z p)) x) :
          TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) = aT := by
      dsimp only [aT, aH, aR]
      exact coneTangent_add (I := I) x r
        (((leviCivitaConnectionGeneral g).cov Y
          ((leviCivitaConnectionGeneral g).cov X Z)) x)
        (-(g.metricInner x (X x) (Z x)) • Y x)
        (-(r : ℝ) * g.metricInner x (Y x)
          (((leviCivitaConnectionGeneral g).cov X Z) x))
        (-(r : ℝ) * Y.dir (fun p => g.metricInner p (X p) (Z p)) x)
    exact hAraw.trans hAadd
  have hB :
      ((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
        ((coneLeviCivitaConnection g).cov (coneHorizontalLift Y)
          (coneHorizontalLift Z))) (x, r) = bT := by
    have hBraw :
        ((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
          ((coneLeviCivitaConnection g).cov (coneHorizontalLift Y)
            (coneHorizontalLift Z))) (x, r) =
          ((((leviCivitaConnectionGeneral g).cov X
                ((leviCivitaConnectionGeneral g).cov Y Z)) x,
              -(r : ℝ) * g.metricInner x (X x)
                (((leviCivitaConnectionGeneral g).cov Y Z) x)) :
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) +
          ((-(g.metricInner x (Y x) (Z x)) • X x,
              -(r : ℝ) *
                X.dir (fun p => g.metricInner p (Y p) (Z p)) x) :
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) := by
      calc
        _ = ((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
            (coneHorizontalLift ((leviCivitaConnectionGeneral g).cov Y Z) +
              coneRadialCorrection g Y Z)) (x, r) :=
          congrArg
            (fun V => ((coneLeviCivitaConnection g).cov
              (coneHorizontalLift X) V) (x, r))
            (coneLeviCivitaConnection_cov_horizontal_horizontal g Y Z)
        _ = (((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
              (coneHorizontalLift ((leviCivitaConnectionGeneral g).cov Y Z))) +
            ((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
              (coneRadialCorrection g Y Z))) (x, r) :=
          congrArg (fun V => V (x, r))
            ((coneLeviCivitaConnection g).add_right (coneHorizontalLift X)
              (coneHorizontalLift ((leviCivitaConnectionGeneral g).cov Y Z))
              (coneRadialCorrection g Y Z))
        _ = ((((leviCivitaConnectionGeneral g).cov X
                ((leviCivitaConnectionGeneral g).cov Y Z)) x,
              -(r : ℝ) * g.metricInner x (X x)
                (((leviCivitaConnectionGeneral g).cov Y Z) x)) :
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) +
          ((-(g.metricInner x (Y x) (Z x)) • X x,
              -(r : ℝ) *
                X.dir (fun p => g.metricInner p (Y p) (Z p)) x) :
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) := by
          rw [SmoothVectorField.add_apply,
            coneLeviCivitaConnection_cov_horizontal_horizontal_apply,
            coneLeviCivitaConnection_cov_horizontal_radialCorrection_apply] <;>
            with_unfolding_all rfl
    have hBadd :
        ((((leviCivitaConnectionGeneral g).cov X
              ((leviCivitaConnectionGeneral g).cov Y Z)) x,
            -(r : ℝ) * g.metricInner x (X x)
              (((leviCivitaConnectionGeneral g).cov Y Z) x)) :
          TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) +
        ((-(g.metricInner x (Y x) (Z x)) • X x,
            -(r : ℝ) * X.dir (fun p => g.metricInner p (Y p) (Z p)) x) :
          TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) = bT := by
      dsimp only [bT, bH, bR]
      exact coneTangent_add (I := I) x r
        (((leviCivitaConnectionGeneral g).cov X
          ((leviCivitaConnectionGeneral g).cov Y Z)) x)
        (-(g.metricInner x (Y x) (Z x)) • X x)
        (-(r : ℝ) * g.metricInner x (X x)
          (((leviCivitaConnectionGeneral g).cov Y Z) x))
        (-(r : ℝ) * X.dir (fun p => g.metricInner p (Y p) (Z p)) x)
    exact hBraw.trans hBadd
  have hC :
      ((coneLeviCivitaConnection g).cov
        (bracketField (coneHorizontalLift X) (coneHorizontalLift Y))
        (coneHorizontalLift Z)) (x, r) = cT := by
    rw [bracketField_coneHorizontalLift_coneHorizontalLift,
      coneLeviCivitaConnection_cov_horizontal_horizontal_apply] <;>
      dsimp only [cT, cH, cR] <;>
      with_unfolding_all rfl
  have hAB := congrArg₂
    (fun u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r) => u - v) hA hB
  have hABC := congrArg₂
    (fun u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r) => u + v) hAB hC
  have hSub : aT - bT = dT := by
    dsimp only [aT, bT, dT]
    exact coneTangent_sub (I := I) x r aH bH aR bR
  have hAdd : dT + cT = outT := by
    dsimp only [dT, cT, outT]
    exact coneTangent_add (I := I) x r (aH - bH) cH (aR - bR) cR
  have hH :
      aH - bH + cH =
        ((leviCivitaConnectionGeneral g).curvature X Y Z) x -
          g.metricInner x (X x) (Z x) • Y x +
          g.metricInner x (Y x) (Z x) • X x := by
    dsimp only [aH, bH, cH]
    rw [(leviCivitaConnectionGeneral g).curvature_apply]
    module
  have hR : aR - bR + cR = 0 := by
    dsimp only [aR, bR, cR]
    have hcompat := (leviCivitaConnectionGeneral_isLeviCivita g).2
    have hYXZ := hcompat Y X Z x
    have hXYZ := hcompat X Y Z x
    have hsym := (leviCivitaConnectionGeneral_isLeviCivita g).1 X Y x
    have hsym_inner := congrArg (fun v => g.metricInner x v (Z x)) hsym
    rw [g.metricInner_sub_left] at hsym_inner
    rw [bracketField_apply]
    linear_combination
      -(r : ℝ) * hYXZ + (r : ℝ) * hXYZ +
        (r : ℝ) * hsym_inner
  have hOut :
      outT =
        ((((leviCivitaConnectionGeneral g).curvature X Y Z) x -
            g.metricInner x (X x) (Z x) • Y x +
            g.metricInner x (Y x) (Z x) • X x, 0) :
          TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) := by
    dsimp only [outT]
    exact congrArg₂
      (fun u : TangentSpace I x => fun s : ℝ =>
        ((u, s) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r))) hH hR
  calc
    _ = ((coneLeviCivitaConnection g).cov (coneHorizontalLift Y)
          ((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
            (coneHorizontalLift Z))) (x, r) -
        ((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
          ((coneLeviCivitaConnection g).cov (coneHorizontalLift Y)
            (coneHorizontalLift Z))) (x, r) +
        ((coneLeviCivitaConnection g).cov
          (bracketField (coneHorizontalLift X) (coneHorizontalLift Y))
          (coneHorizontalLift Z)) (x, r) :=
      (coneLeviCivitaConnection g).curvature_apply _ _ _ _
    _ = aT - bT + cT := hABC
    _ = dT + cT := congrArg (fun q => q + cT) hSub
    _ = outT := hAdd
    _ = _ := hOut

/-- **Math.** The all-horizontal component of the cone curvature form is
`r²` times the base curvature form minus the metric exterior-square form. -/
theorem coneCurvatureForm_horizontal
    (g : RiemannianMetric I N) (X Y Z W : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    curvatureFormAt (coneMetric g) (coneLeviCivitaConnection g) (x, r)
        (coneHorizontalLift X (x, r)) (coneHorizontalLift Y (x, r))
        (coneHorizontalLift Z (x, r)) (coneHorizontalLift W (x, r)) =
      (r : ℝ) ^ 2 *
        (curvatureFormAt g (leviCivitaConnectionGeneral g) x
            (X x) (Y x) (Z x) (W x) -
          (g.metricInner x (X x) (Z x) * g.metricInner x (Y x) (W x) -
            g.metricInner x (Y x) (Z x) * g.metricInner x (X x) (W x))) := by
  rw [curvatureFormAt_eq (coneMetric g) (coneLeviCivitaConnection g)
      (coneHorizontalLift X) (coneHorizontalLift Y)
      (coneHorizontalLift Z) (coneHorizontalLift W) (x, r),
    Riemannian.AffineConnection.curvatureForm,
    coneCurvature_horizontal_horizontal_horizontal_apply,
    coneMetric_metricInner_prod, coneHorizontalLift_apply,
    curvatureFormAt_eq g (leviCivitaConnectionGeneral g) X Y Z W x,
    Riemannian.AffineConnection.curvatureForm]
  simp only [mul_zero, add_zero, g.metricInner_sub_left,
    g.metricInner_add_left, g.metricInner_smul_left]
  ring

/-- **Math.** A curvature-form component with three horizontal arguments and
one radial argument vanishes. -/
theorem coneCurvatureForm_horizontal_horizontal_horizontal_radial
    (g : RiemannianMetric I N) (X Y Z : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    curvatureFormAt (coneMetric g) (coneLeviCivitaConnection g) (x, r)
        (coneHorizontalLift X (x, r)) (coneHorizontalLift Y (x, r))
        (coneHorizontalLift Z (x, r))
        (coneRadialField (I := I) (N := N) (x, r)) = 0 := by
  rw [curvatureFormAt_eq (coneMetric g) (coneLeviCivitaConnection g)
      (coneHorizontalLift X) (coneHorizontalLift Y) (coneHorizontalLift Z)
      (coneRadialField (I := I) (N := N)) (x, r),
    Riemannian.AffineConnection.curvatureForm,
    coneCurvature_horizontal_horizontal_horizontal_apply,
    coneMetric_any_radial]

/-- **Math.** The curvature form vanishes on two mixed radial bivectors. -/
theorem coneCurvatureForm_horizontal_radial_horizontal_radial
    (g : RiemannianMetric I N) (X Y : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    curvatureFormAt (coneMetric g) (coneLeviCivitaConnection g) (x, r)
        (coneHorizontalLift X (x, r))
        (coneRadialField (I := I) (N := N) (x, r))
        (coneHorizontalLift Y (x, r))
        (coneRadialField (I := I) (N := N) (x, r)) = 0 := by
  rw [curvatureFormAt_antisymm_right (coneMetric g)
      (coneLeviCivitaConnection g) (coneLeviCivitaConnection_isLeviCivita g).2
      (x, r) (coneHorizontalLift X (x, r))
      (coneRadialField (I := I) (N := N) (x, r))
      (coneHorizontalLift Y (x, r))
      (coneRadialField (I := I) (N := N) (x, r)),
    curvatureFormAt_eq (coneMetric g) (coneLeviCivitaConnection g)
      (coneHorizontalLift X) (coneRadialField (I := I) (N := N))
      (coneRadialField (I := I) (N := N)) (coneHorizontalLift Y) (x, r),
    Riemannian.AffineConnection.curvatureForm,
    coneCurvature_horizontal_radial_radial]
  simp

/-- **Math.** The actual curvature bilinear form on the exterior square of a
cone tangent fibre. -/
noncomputable def coneCurvatureOperatorAt
    (g : RiemannianMetric I N) (q : N × ↥positiveReal) :
    ⋀[ℝ]^2 (TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) →ₗ[ℝ]
      ⋀[ℝ]^2 (TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) →ₗ[ℝ] ℝ := by
  letI : Bundle.RiemannianBundle
      (TangentSpace (I.prod 𝓘(ℝ, ℝ)) : N × ↥positiveReal → Type _) :=
    ⟨(coneMetric g).toRiemannianMetric⟩
  exact curvatureOperator
    (isAlgCurvatureForm_curvatureFormAt (coneMetric g)
      (coneLeviCivitaConnection g) (coneLeviCivitaConnection_isLeviCivita g) q)

set_option maxHeartbeats 800000 in
/-- **Math.** The cone curvature operator evaluates on decomposable bivectors
as the pointwise cone curvature form. -/
@[simp] theorem coneCurvatureOperatorAt_ιMulti
    (g : RiemannianMetric I N) (q : N × ↥positiveReal)
    (a b c d : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) :
    coneCurvatureOperatorAt g q (ιMulti ℝ 2 ![a, b]) (ιMulti ℝ 2 ![c, d]) =
      curvatureFormAt (coneMetric g) (coneLeviCivitaConnection g) q a b c d := by
  letI : Bundle.RiemannianBundle
      (TangentSpace (I.prod 𝓘(ℝ, ℝ)) : N × ↥positiveReal → Type _) :=
    ⟨(coneMetric g).toRiemannianMetric⟩
  rw [coneCurvatureOperatorAt, curvatureOperator_ιMulti]

/-- **Math.** The base block `Rm_g - Λ²g` at a point of the cone base. -/
noncomputable def coneBaseCurvatureDifferenceAt
    (g : RiemannianMetric I N) (x : N) :
    ⋀[ℝ]^2 (TangentSpace I x) →ₗ[ℝ]
      ⋀[ℝ]^2 (TangentSpace I x) →ₗ[ℝ] ℝ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : N → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact curvatureOperator
      (isAlgCurvatureForm_curvatureFormAt g (leviCivitaConnectionGeneral g)
        (leviCivitaConnectionGeneral_isLeviCivita g) x) -
    curvatureOperator Riemannian.isAlgCurvatureForm_stdCurvForm

/-- **Math.** Projection of a cone tangent fibre onto its horizontal base
component. -/
def coneTangentHorizontalProjection (x : N) (r : ↥positiveReal) :
    TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r) →ₗ[ℝ] TangentSpace I x where
  toFun v := v.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Math.** Inclusion of the horizontal tangent subspace in a cone tangent
fibre. -/
def coneTangentHorizontalInclusion (x : N) (r : ↥positiveReal) :
    TangentSpace I x →ₗ[ℝ] TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r) where
  toFun u := (u, 0)
  map_add' u v := by
    calc
      _ = ((u + v, (0 : ℝ) + 0) :
          TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) :=
        coneTangent_ext (I := I) x r rfl (add_zero 0).symm
      _ = _ := (coneTangent_add (I := I) x r u v 0 0).symm
  map_smul' c u := by
    apply Eq.symm
    calc
      _ = ((c • u, c • (0 : ℝ)) :
          TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) :=
        coneTangent_smul (I := I) x r c u 0
      _ = _ := coneTangent_ext (I := I) x r rfl (smul_zero c)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ N]
    [I.Boundaryless] [SigmaCompactSpace N] [T2Space N] in
@[simp] theorem coneTangentHorizontalInclusion_apply
    (x : N) (r : ↥positiveReal) (u : TangentSpace I x) :
    coneTangentHorizontalInclusion x r u =
      ((u, 0) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) :=
  rfl

/-- **Math.** The inner product on the exterior square of a cone tangent
fibre induced by the cone metric. -/
noncomputable def coneWedgeInnerAt
    (g : RiemannianMetric I N) (q : N × ↥positiveReal) :
    ⋀[ℝ]^2 (TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) →ₗ[ℝ]
      ⋀[ℝ]^2 (TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) →ₗ[ℝ] ℝ := by
  letI : Bundle.RiemannianBundle
      (TangentSpace (I.prod 𝓘(ℝ, ℝ)) : N × ↥positiveReal → Type _) :=
    ⟨(coneMetric g).toRiemannianMetric⟩
  exact wedgeInner

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N] in
/-- **Math.** On decomposable bivectors, `coneWedgeInnerAt` is the determinant
of the cone metric pairings. -/
theorem coneWedgeInnerAt_ιMulti
    (g : RiemannianMetric I N) (q : N × ↥positiveReal)
    (a b c d : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) :
    coneWedgeInnerAt g q (ιMulti ℝ 2 ![a, b]) (ιMulti ℝ 2 ![c, d]) =
      (coneMetric g).metricInner q a c * (coneMetric g).metricInner q b d -
        (coneMetric g).metricInner q b c * (coneMetric g).metricInner q a d := by
  letI : Bundle.RiemannianBundle
      (TangentSpace (I.prod 𝓘(ℝ, ℝ)) : N × ↥positiveReal → Type _) :=
    ⟨(coneMetric g).toRiemannianMetric⟩
  rw [coneWedgeInnerAt, wedgeInner_ιMulti]
  rfl

/-- **Math.** A decomposable horizontal cone bivector is orthogonal to every
mixed radial bivector for the cone-induced exterior inner product. -/
theorem coneWedgeInnerAt_horizontal_mixed_generator
    (g : RiemannianMetric I N) (x : N) (r : ↥positiveReal)
    (u v z : TangentSpace I x) :
    coneWedgeInnerAt g (x, r)
        (ιMulti ℝ 2 ![(u, (0 : ℝ)), (v, (0 : ℝ))])
        (ιMulti ℝ 2 ![(z, (0 : ℝ)),
          ((0 : TangentSpace I x), (1 : ℝ))]) = 0 := by
  rw [coneWedgeInnerAt_ιMulti]
  simp only [coneMetric_metricInner_mk, g.metricInner_zero_right, mul_zero,
    add_zero, zero_mul, sub_zero]

/-- **Math.** The two summands in the canonical cone splitting are
orthogonal: every horizontal `2`-vector is perpendicular to every
`z ∧ ∂r`. -/
theorem coneWedgeInnerAt_horizontal_mixed
    (g : RiemannianMetric I N) (x : N) (r : ↥positiveReal)
    (φ : ⋀[ℝ]^2 (TangentSpace I x)) (z : TangentSpace I x) :
    coneWedgeInnerAt g (x, r)
        (exteriorPower.map 2 (coneTangentHorizontalInclusion x r) φ)
        (ιMulti ℝ 2 ![(z, (0 : ℝ)),
          ((0 : TangentSpace I x), (1 : ℝ))]) = 0 := by
  have hzero :
      ((coneWedgeInnerAt g (x, r)).flip
          (ιMulti ℝ 2 ![(z, (0 : ℝ)),
            ((0 : TangentSpace I x), (1 : ℝ))])).comp
        (exteriorPower.map 2 (coneTangentHorizontalInclusion x r)) = 0 := by
    apply exteriorPower.linearMap_ext
    ext w
    have hw : w = ![w 0, w 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hw]
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, LinearMap.zero_apply, LinearMap.flip_apply]
    have hmap :
        (⇑(coneTangentHorizontalInclusion (I := I) x r) ∘ ![w 0, w 1]) =
          ![((w 0), (0 : ℝ)), ((w 1), (0 : ℝ))] := by
      funext i
      fin_cases i
      · exact coneTangentHorizontalInclusion_apply x r (w 0)
      · exact coneTangentHorizontalInclusion_apply x r (w 1)
    rw [hmap]
    exact coneWedgeInnerAt_horizontal_mixed_generator g x r (w 0) (w 1) z
  have h := LinearMap.congr_fun hzero φ
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.flip_apply] using h

/-- **Math.** The pointwise cone block form `diag(r² A, 0)`, defined directly
on the cone tangent fibre. -/
noncomputable def coneCurvatureBlockFormAt
    (g : RiemannianMetric I N) (x : N) (r : ↥positiveReal) :
    ⋀[ℝ]^2 (TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) →ₗ[ℝ]
      ⋀[ℝ]^2 (TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun φ ψ => (r : ℝ) ^ 2 * coneBaseCurvatureDifferenceAt g x
      (exteriorPower.map 2 (coneTangentHorizontalProjection x r) φ)
      (exteriorPower.map 2 (coneTangentHorizontalProjection x r) ψ))
    (by intros; simp; ring)
    (by intros; simp; ring)
    (by intros; simp; ring)
    (by intros; simp; ring)

@[simp] theorem coneCurvatureBlockFormAt_apply
    (g : RiemannianMetric I N) (x : N) (r : ↥positiveReal)
    (φ ψ : ⋀[ℝ]^2 (TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r))) :
    coneCurvatureBlockFormAt g x r φ ψ =
      (r : ℝ) ^ 2 * coneBaseCurvatureDifferenceAt g x
        (exteriorPower.map 2 (coneTangentHorizontalProjection x r) φ)
        (exteriorPower.map 2 (coneTangentHorizontalProjection x r) ψ) :=
  rfl

/-- **Math.** On two horizontal decomposable bivectors, the cone curvature
operator is `r²` times `Rm_g - Λ²g`. -/
theorem coneCurvatureOperatorAt_horizontal
    (g : RiemannianMetric I N) (X Y Z W : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    coneCurvatureOperatorAt g (x, r)
        (ιMulti ℝ 2 ![coneHorizontalLift X (x, r),
          coneHorizontalLift Y (x, r)])
        (ιMulti ℝ 2 ![coneHorizontalLift Z (x, r),
          coneHorizontalLift W (x, r)]) =
      (r : ℝ) ^ 2 * coneBaseCurvatureDifferenceAt g x
        (ιMulti ℝ 2 ![X x, Y x]) (ιMulti ℝ 2 ![Z x, W x]) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : N → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle
      (TangentSpace (I.prod 𝓘(ℝ, ℝ)) : N × ↥positiveReal → Type _) :=
    ⟨(coneMetric g).toRiemannianMetric⟩
  rw [coneCurvatureOperatorAt, coneBaseCurvatureDifferenceAt]
  simp only [curvatureOperator_ιMulti, LinearMap.sub_apply]
  rw [coneCurvatureForm_horizontal]
  rfl

/-- **Math.** Pointwise tangent-vector form of the horizontal cone-curvature
block. -/
theorem coneCurvatureOperatorAt_horizontal_tangent
    (g : RiemannianMetric I N) (x : N) (r : ↥positiveReal)
    (u v z w : TangentSpace I x) :
    coneCurvatureOperatorAt g (x, r)
        (ιMulti ℝ 2 ![(u, (0 : ℝ)), (v, (0 : ℝ))])
        (ιMulti ℝ 2 ![(z, (0 : ℝ)), (w, (0 : ℝ))]) =
      (r : ℝ) ^ 2 * coneBaseCurvatureDifferenceAt g x
        (ιMulti ℝ 2 ![u, v]) (ιMulti ℝ 2 ![z, w]) := by
  have h := coneCurvatureOperatorAt_horizontal g
    (extendVector x u) (extendVector x v) (extendVector x z) (extendVector x w) x r
  simp only [coneHorizontalLift_apply, extendVector_apply] at h
  with_unfolding_all exact h

/-- **Math.** A horizontal cone bivector is curvature-orthogonal to every
mixed radial bivector. -/
theorem coneCurvatureOperatorAt_horizontal_mixed_decomposable
    (g : RiemannianMetric I N) (x : N) (r : ↥positiveReal)
    (u v z : TangentSpace I x) :
    coneCurvatureOperatorAt g (x, r)
        (ιMulti ℝ 2 ![(u, (0 : ℝ)), (v, (0 : ℝ))])
        (ιMulti ℝ 2 ![(z, (0 : ℝ)),
          ((0 : TangentSpace I x), (1 : ℝ))]) = 0 := by
  calc
    coneCurvatureOperatorAt g (x, r)
        (ιMulti ℝ 2 ![(u, (0 : ℝ)), (v, (0 : ℝ))])
        (ιMulti ℝ 2 ![(z, (0 : ℝ)),
          ((0 : TangentSpace I x), (1 : ℝ))]) =
        curvatureFormAt (coneMetric g) (coneLeviCivitaConnection g) (x, r)
          (u, 0) (v, 0) (z, 0) (0, 1) :=
      coneCurvatureOperatorAt_ιMulti g (x, r) _ _ _ _
    _ = 0 := by
      have h := coneCurvatureForm_horizontal_horizontal_horizontal_radial g
        (extendVector x u) (extendVector x v) (extendVector x z) x r
      simp only [coneHorizontalLift_apply, coneRadialField_apply, extendVector_apply] at h
      with_unfolding_all exact h

set_option maxHeartbeats 4000000 in
/-- **Math.** Canonical-splitting form of the horizontal-mixed vanishing
component. -/
theorem coneCurvatureOperatorAt_horizontal_mixed
    (g : RiemannianMetric I N) (x : N) (r : ↥positiveReal)
    (u v z : TangentSpace I x) :
    coneCurvatureOperatorAt g (x, r)
        (ιMulti ℝ 2 ![(u, (0 : ℝ)), (v, (0 : ℝ))])
        (coneWedgeMixed (V := TangentSpace I x) z) = 0 := by
  rw [coneWedgeMixed_apply (V := TangentSpace I x)]
  exact coneCurvatureOperatorAt_horizontal_mixed_decomposable g x r u v z

/-- **Math.** The mixed-horizontal cone-curvature block vanishes. -/
theorem coneCurvatureOperatorAt_mixed_horizontal_decomposable
    (g : RiemannianMetric I N) (x : N) (r : ↥positiveReal)
    (u z w : TangentSpace I x) :
    coneCurvatureOperatorAt g (x, r)
        (ιMulti ℝ 2 ![(u, (0 : ℝ)),
          ((0 : TangentSpace I x), (1 : ℝ))])
        (ιMulti ℝ 2 ![(z, (0 : ℝ)), (w, (0 : ℝ))]) = 0 := by
  letI : Bundle.RiemannianBundle
      (TangentSpace (I.prod 𝓘(ℝ, ℝ)) : N × ↥positiveReal → Type _) :=
    ⟨(coneMetric g).toRiemannianMetric⟩
  calc
    coneCurvatureOperatorAt g (x, r)
          (ιMulti ℝ 2 ![(u, (0 : ℝ)), ((0 : TangentSpace I x), (1 : ℝ))])
          (ιMulti ℝ 2 ![(z, (0 : ℝ)), (w, (0 : ℝ))]) =
        curvatureFormAt (coneMetric g) (coneLeviCivitaConnection g) (x, r)
          (u, 0) (0, 1) (z, 0) (w, 0) :=
      coneCurvatureOperatorAt_ιMulti g (x, r) _ _ _ _
    _ = curvatureFormAt (coneMetric g) (coneLeviCivitaConnection g) (x, r)
          (z, 0) (w, 0) (u, 0) (0, 1) :=
      (isAlgCurvatureForm_curvatureFormAt (coneMetric g)
        (coneLeviCivitaConnection g) (coneLeviCivitaConnection_isLeviCivita g)
        (x, r)).pairSwap _ _ _ _
    _ = 0 := by
      have h := coneCurvatureForm_horizontal_horizontal_horizontal_radial g
        (extendVector x z) (extendVector x w) (extendVector x u) x r
      simp only [coneHorizontalLift_apply, coneRadialField_apply, extendVector_apply] at h
      with_unfolding_all exact h

set_option maxHeartbeats 4000000 in
/-- **Math.** Canonical-splitting form of the mixed-horizontal vanishing
component. -/
theorem coneCurvatureOperatorAt_mixed_horizontal
    (g : RiemannianMetric I N) (x : N) (r : ↥positiveReal)
    (u z w : TangentSpace I x) :
    coneCurvatureOperatorAt g (x, r)
        (coneWedgeMixed (V := TangentSpace I x) u)
        (ιMulti ℝ 2 ![(z, (0 : ℝ)), (w, (0 : ℝ))]) = 0 := by
  rw [coneWedgeMixed_apply (V := TangentSpace I x)]
  exact coneCurvatureOperatorAt_mixed_horizontal_decomposable g x r u z w

/-- **Math.** The mixed radial block of the cone curvature operator is zero. -/
theorem coneCurvatureOperatorAt_mixed_mixed_decomposable
    (g : RiemannianMetric I N) (x : N) (r : ↥positiveReal)
    (u v : TangentSpace I x) :
    coneCurvatureOperatorAt g (x, r)
        (ιMulti ℝ 2 ![(u, (0 : ℝ)),
          ((0 : TangentSpace I x), (1 : ℝ))])
        (ιMulti ℝ 2 ![(v, (0 : ℝ)),
          ((0 : TangentSpace I x), (1 : ℝ))]) = 0 := by
  calc
    coneCurvatureOperatorAt g (x, r)
        (ιMulti ℝ 2 ![(u, (0 : ℝ)),
          ((0 : TangentSpace I x), (1 : ℝ))])
        (ιMulti ℝ 2 ![(v, (0 : ℝ)),
          ((0 : TangentSpace I x), (1 : ℝ))]) =
        curvatureFormAt (coneMetric g) (coneLeviCivitaConnection g) (x, r)
          (u, 0) (0, 1) (v, 0) (0, 1) :=
      coneCurvatureOperatorAt_ιMulti g (x, r) _ _ _ _
    _ = 0 := by
      have h := coneCurvatureForm_horizontal_radial_horizontal_radial g
        (extendVector x u) (extendVector x v) x r
      simp only [coneHorizontalLift_apply, coneRadialField_apply, extendVector_apply] at h
      with_unfolding_all exact h

set_option maxHeartbeats 4000000 in
/-- **Math.** Canonical-splitting form of the mixed-mixed vanishing component. -/
theorem coneCurvatureOperatorAt_mixed_mixed
    (g : RiemannianMetric I N) (x : N) (r : ↥positiveReal)
    (u v : TangentSpace I x) :
    coneCurvatureOperatorAt g (x, r)
        (coneWedgeMixed (V := TangentSpace I x) u)
        (coneWedgeMixed (V := TangentSpace I x) v) = 0 := by
  rw [coneWedgeMixed_apply (V := TangentSpace I x),
    coneWedgeMixed_apply (V := TangentSpace I x)]
  exact coneCurvatureOperatorAt_mixed_mixed_decomposable g x r u v

set_option maxHeartbeats 4000000 in
/-- **Math.** With respect to the canonical splitting
`Λ²(T_xN × ℝ∂r) = Λ²T_xN ⊕ (T_xN ∧ ∂r)`, the actual cone
curvature operator is `diag(r² (Rm_g - Λ²g), 0)`. -/
theorem coneCurvatureOperatorAt_eq_block
    (g : RiemannianMetric I N) (x : N) (r : ↥positiveReal) :
    coneCurvatureOperatorAt g (x, r) =
      coneCurvatureBlockFormAt g x r := by
  refine exteriorPower.linearMap_ext
    (f := coneCurvatureOperatorAt g (x, r))
    (g := coneCurvatureBlockFormAt g x r) ?_
  apply DFunLike.ext _ _
  intro a
  refine exteriorPower.linearMap_ext
    (f := coneCurvatureOperatorAt g (x, r) (ιMulti ℝ 2 a))
    (g := coneCurvatureBlockFormAt g x r (ιMulti ℝ 2 a)) ?_
  apply DFunLike.ext _ _
  intro b
  have ha : a = ![a 0, a 1] := by
    funext i
    fin_cases i <;> rfl
  have hb : b = ![b 0, b 1] := by
    funext i
    fin_cases i <;> rfl
  rw [ha, hb]
  simp only [LinearMap.compAlternatingMap_apply]
  rw [coneCurvatureBlockFormAt_apply,
    exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti]
  change coneCurvatureOperatorAt g (x, r)
      (ιMulti ℝ 2 ![a 0, a 1]) (ιMulti ℝ 2 ![b 0, b 1]) =
    (r : ℝ) ^ 2 * coneBaseCurvatureDifferenceAt g x
      (ιMulti ℝ 2 ![(a 0).1, (a 1).1])
      (ιMulti ℝ 2 ![(b 0).1, (b 1).1])
  calc
    coneCurvatureOperatorAt g (x, r)
        (ιMulti ℝ 2 ![a 0, a 1]) (ιMulti ℝ 2 ![b 0, b 1]) =
      coneCurvatureOperatorAt g (x, r)
        (exteriorPower.map 2 (LinearMap.inl ℝ (TangentSpace I x) ℝ)
            (ιMulti ℝ 2 ![(a 0).1, (a 1).1]) +
          coneWedgeMixed (V := TangentSpace I x)
            ((a 1).2 • (a 0).1 - (a 0).2 • (a 1).1))
        (ιMulti ℝ 2 ![b 0, b 1]) :=
      congrArg
        (fun φ => coneCurvatureOperatorAt g (x, r) φ
          (ιMulti ℝ 2 ![b 0, b 1]))
        (coneWedge_iMulti_decomp (V := TangentSpace I x) (a 0) (a 1))
    _ = coneCurvatureOperatorAt g (x, r)
        (exteriorPower.map 2 (LinearMap.inl ℝ (TangentSpace I x) ℝ)
            (ιMulti ℝ 2 ![(a 0).1, (a 1).1]) +
          coneWedgeMixed (V := TangentSpace I x)
            ((a 1).2 • (a 0).1 - (a 0).2 • (a 1).1))
        (exteriorPower.map 2 (LinearMap.inl ℝ (TangentSpace I x) ℝ)
            (ιMulti ℝ 2 ![(b 0).1, (b 1).1]) +
          coneWedgeMixed (V := TangentSpace I x)
            ((b 1).2 • (b 0).1 - (b 0).2 • (b 1).1)) :=
      congrArg
        (coneCurvatureOperatorAt g (x, r)
          (exteriorPower.map 2 (LinearMap.inl ℝ (TangentSpace I x) ℝ)
              (ιMulti ℝ 2 ![(a 0).1, (a 1).1]) +
            coneWedgeMixed (V := TangentSpace I x)
              ((a 1).2 • (a 0).1 - (a 0).2 • (a 1).1)))
        (coneWedge_iMulti_decomp (V := TangentSpace I x) (b 0) (b 1))
    _ = (r : ℝ) ^ 2 * coneBaseCurvatureDifferenceAt g x
        (ιMulti ℝ 2 ![(a 0).1, (a 1).1])
        (ιMulti ℝ 2 ![(b 0).1, (b 1).1]) := by
      have hmapa :
          (⇑(LinearMap.inl ℝ (TangentSpace I x) ℝ) ∘ ![(a 0).1, (a 1).1]) =
            ![((a 0).1, (0 : ℝ)), ((a 1).1, (0 : ℝ))] := by
        funext i
        fin_cases i <;> rfl
      have hmapb :
          (⇑(LinearMap.inl ℝ (TangentSpace I x) ℝ) ∘ ![(b 0).1, (b 1).1]) =
            ![((b 0).1, (0 : ℝ)), ((b 1).1, (0 : ℝ))] := by
        funext i
        fin_cases i <;> rfl
      simp only [exteriorPower.map_apply_ιMulti]
      rw [hmapa, hmapb]
      let aH : ⋀[ℝ]^2 (TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) :=
        ιMulti ℝ 2 ![((a 0).1, (0 : ℝ)), ((a 1).1, (0 : ℝ))]
      let aM : ⋀[ℝ]^2 (TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) :=
        coneWedgeMixed ((a 1).2 • (a 0).1 - (a 0).2 • (a 1).1)
      let bH : ⋀[ℝ]^2 (TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) :=
        ιMulti ℝ 2 ![((b 0).1, (0 : ℝ)), ((b 1).1, (0 : ℝ))]
      let bM : ⋀[ℝ]^2 (TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) :=
        coneWedgeMixed ((b 1).2 • (b 0).1 - (b 0).2 • (b 1).1)
      change coneCurvatureOperatorAt g (x, r) (aH + aM) (bH + bM) = _
      have hhh : coneCurvatureOperatorAt g (x, r) aH bH =
          (r : ℝ) ^ 2 * coneBaseCurvatureDifferenceAt g x
            (ιMulti ℝ 2 ![(a 0).1, (a 1).1])
            (ιMulti ℝ 2 ![(b 0).1, (b 1).1]) := by
        have h := coneCurvatureOperatorAt_horizontal_tangent (I := I) g x r
          (a 0).1 (a 1).1 (b 0).1 (b 1).1
        with_unfolding_all exact h
      have hhm : coneCurvatureOperatorAt g (x, r) aH bM = 0 := by
        have h := coneCurvatureOperatorAt_horizontal_mixed (I := I) g x r
          (a 0).1 (a 1).1 ((b 1).2 • (b 0).1 - (b 0).2 • (b 1).1)
        with_unfolding_all exact h
      have hmh : coneCurvatureOperatorAt g (x, r) aM bH = 0 := by
        have h := coneCurvatureOperatorAt_mixed_horizontal (I := I) g x r
          ((a 1).2 • (a 0).1 - (a 0).2 • (a 1).1) (b 0).1 (b 1).1
        with_unfolding_all exact h
      have hmm : coneCurvatureOperatorAt g (x, r) aM bM = 0 := by
        have h := coneCurvatureOperatorAt_mixed_mixed (I := I) g x r
          ((a 1).2 • (a 0).1 - (a 0).2 • (a 1).1)
          ((b 1).2 • (b 0).1 - (b 0).2 • (b 1).1)
        with_unfolding_all exact h
      calc
        _ = (coneCurvatureOperatorAt g (x, r) aH +
              coneCurvatureOperatorAt g (x, r) aM) (bH + bM) := by
          exact congrArg (fun L => L (bH + bM))
            ((coneCurvatureOperatorAt g (x, r)).map_add aH aM)
        _ = coneCurvatureOperatorAt g (x, r) aH (bH + bM) +
              coneCurvatureOperatorAt g (x, r) aM (bH + bM) := by
          rw [LinearMap.add_apply]
        _ = (coneCurvatureOperatorAt g (x, r) aH bH +
                coneCurvatureOperatorAt g (x, r) aH bM) +
              (coneCurvatureOperatorAt g (x, r) aM bH +
                coneCurvatureOperatorAt g (x, r) aM bM) := by
          exact congrArg₂ (· + ·)
            ((coneCurvatureOperatorAt g (x, r) aH).map_add bH bM)
            ((coneCurvatureOperatorAt g (x, r) aM).map_add bH bM)
        _ = ((r : ℝ) ^ 2 * coneBaseCurvatureDifferenceAt g x
              (ιMulti ℝ 2 ![(a 0).1, (a 1).1])
              (ιMulti ℝ 2 ![(b 0).1, (b 1).1]) + 0) + (0 + 0) :=
          congrArg₂ (· + ·) (congrArg₂ (· + ·) hhh hhm)
            (congrArg₂ (· + ·) hmh hmm)
        _ = _ := by simp only [add_zero]

end ConeCurvature

end MorganTianLib
