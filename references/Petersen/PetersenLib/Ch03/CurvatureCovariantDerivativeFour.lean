import PetersenLib.Ch03.CurvaturePointwise

/-!
# Petersen Ch. 3, §3.1.5 — the covariant derivative of the `(0,4)`-curvature

The covariant derivative of the `(0,4)`-curvature tensor
`(∇_X R)(Y,Z,V,U) = D_X(R(Y,Z,V,U)) − R(∇_X Y,Z,V,U) − R(Y,∇_X Z,V,U)
− R(Y,Z,∇_X V,U) − R(Y,Z,V,∇_X U)` (`covariantDerivativeCurvatureFour`),
its identification with the `(1,3)` covariant derivative through the metric
(`covariantDerivativeCurvatureFour_eq_metricInner`, by metric compatibility),
the second Bianchi identity at the `(0,4)` level
(`covariantDerivativeCurvatureFour_secondBianchi`), and the algebraic
symmetries `∇R` inherits from `R` (antisymmetry in each pair, pair swap).

These are the inputs for the contracted Bianchi identity (Prop. 3.1.5).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.1, §3.1.5.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]

/-! ## Smoothness of the `(0,4)`-curvature as a function -/

/-- `R(X,Y,Z,W) : M → ℝ` is smooth for smooth arguments. -/
theorem contMDiff_curvatureTensorFour {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {X Y Z W : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (hW : IsSmoothVectorField W) :
    ContMDiff I 𝓘(ℝ) ∞ (curvatureTensorFour D X Y Z W) := by
  have hR : IsSmoothVectorField (curvatureTensor D.toAffineConnection X Y Z) :=
    hX.curvatureTensor hY hZ
  have h := (metricOperator_isTensorOperator g).smooth_eval
    ![curvatureTensor D.toAffineConnection X Y Z, W]
    (by
      intro i
      fin_cases i
      · simpa using hR
      · simpa using hW)
  have e : (metricOperator g ![curvatureTensor D.toAffineConnection X Y Z, W] : M → ℝ)
      = curvatureTensorFour D X Y Z W := by
    funext q
    simp [metricOperator, curvatureTensorFour_apply]
  rwa [e] at h

/-! ## The covariant derivative of the `(0,4)`-curvature tensor -/

/-- **Math.** The **covariant derivative of the `(0,4)`-curvature tensor**
(Petersen §2.2.2 applied to `R⁴`): the Leibniz-defined `(0,5)`-tensor
`(∇_X R)(Y,Z,V,U) = D_X(R(Y,Z,V,U)) − R(∇_X Y,Z,V,U) − R(Y,∇_X Z,V,U)
− R(Y,Z,∇_X V,U) − R(Y,Z,V,∇_X U)`. -/
def covariantDerivativeCurvatureFour {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (X Y Z V U : Π x : M, TangentSpace I x) :
    M → ℝ :=
  fun p => directionalDerivative X (curvatureTensorFour D Y Z V U) p
    - curvatureTensorFour D (D.toAffineConnection.covField X Y) Z V U p
    - curvatureTensorFour D Y (D.toAffineConnection.covField X Z) V U p
    - curvatureTensorFour D Y Z (D.toAffineConnection.covField X V) U p
    - curvatureTensorFour D Y Z V (D.toAffineConnection.covField X U) p

omit [I.Boundaryless] [CompleteSpace E] in
theorem covariantDerivativeCurvatureFour_apply {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (X Y Z V U : Π x : M, TangentSpace I x)
    (p : M) :
    covariantDerivativeCurvatureFour D X Y Z V U p
      = directionalDerivative X (curvatureTensorFour D Y Z V U) p
        - curvatureTensorFour D (D.toAffineConnection.covField X Y) Z V U p
        - curvatureTensorFour D Y (D.toAffineConnection.covField X Z) V U p
        - curvatureTensorFour D Y Z (D.toAffineConnection.covField X V) U p
        - curvatureTensorFour D Y Z V (D.toAffineConnection.covField X U) p := rfl

/-- **Math.** `(∇_X R)(Y,Z,V,U) = g((∇_X R)(Y,Z)V, U)`: the `(0,4)` covariant
derivative is the metric pairing of the `(1,3)` covariant derivative — by
metric compatibility, differentiating `R(Y,Z,V,U) = g(R(Y,Z)V, U)` produces
exactly the last Leibniz correction `R(Y,Z,V,∇_X U)` next to
`g(∇_X(R(Y,Z)V), U)`. -/
theorem covariantDerivativeCurvatureFour_eq_metricInner
    {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {X Y Z V U : Π x : M, TangentSpace I x}
    (hY : IsSmoothVectorField Y) (hZ : IsSmoothVectorField Z)
    (hV : IsSmoothVectorField V) (hU : IsSmoothVectorField U) (p : M) :
    covariantDerivativeCurvatureFour D X Y Z V U p
      = g.metricInner p
          (covariantDerivativeCurvature D.toAffineConnection X Y Z V p) (U p) := by
  have hR : IsSmoothVectorField (curvatureTensor D.toAffineConnection Y Z V) :=
    hY.curvatureTensor hZ hV
  -- metric compatibility on the pair (R(Y,Z)V, U)
  have hcompat := D.metric_compat hR hU p (X p)
  rw [dirTangent_eq_directionalDerivative] at hcompat
  have hdd : directionalDerivative X (curvatureTensorFour D Y Z V U) p
      = g.metricInner p
          (D.cov p (X p) (curvatureTensor D.toAffineConnection Y Z V)) (U p)
        + g.metricInner p (curvatureTensor D.toAffineConnection Y Z V p)
            (D.cov p (X p) U) := hcompat
  -- expand ∇_X(R(Y,Z)V) via the (1,3) covariant derivative
  have hexp := covariantDerivativeCurvature_apply D.toAffineConnection X Y Z V p
  have hcov : D.cov p (X p) (curvatureTensor D.toAffineConnection Y Z V)
      = covariantDerivativeCurvature D.toAffineConnection X Y Z V p
        + curvatureTensor D.toAffineConnection
            (D.toAffineConnection.covField X Y) Z V p
        + curvatureTensor D.toAffineConnection Y
            (D.toAffineConnection.covField X Z) V p
        + curvatureTensor D.toAffineConnection Y Z
            (D.toAffineConnection.covField X V) p := by
    rw [hexp]
    module
  rw [covariantDerivativeCurvatureFour_apply, hdd, hcov]
  simp only [curvatureTensorFour_apply, g.metricInner_add_left,
    AffineConnection.covField_apply]
  ring

/-! ## The second Bianchi identity at the `(0,4)` level -/

/-- **Math.** **Bianchi's second identity** for the `(0,4)`-curvature tensor:
`(∇_X R)(Y,Z,V,U) + (∇_Y R)(Z,X,V,U) + (∇_Z R)(X,Y,V,U) = 0`. -/
theorem covariantDerivativeCurvatureFour_secondBianchi
    {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {X Y Z V U : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (hV : IsSmoothVectorField V)
    (hU : IsSmoothVectorField U) (p : M) :
    covariantDerivativeCurvatureFour D X Y Z V U p
      + covariantDerivativeCurvatureFour D Y Z X V U p
      + covariantDerivativeCurvatureFour D Z X Y V U p = 0 := by
  rw [covariantDerivativeCurvatureFour_eq_metricInner D hY hZ hV hU p,
    covariantDerivativeCurvatureFour_eq_metricInner D hZ hX hV hU p,
    covariantDerivativeCurvatureFour_eq_metricInner D hX hY hV hU p,
    ← g.metricInner_add_left, ← g.metricInner_add_left,
    curvatureTensor_secondBianchi D hX hY hZ hV p, g.metricInner_zero_left]

/-! ## Inherited algebraic symmetries of `∇R` -/

/-- `∇R` is antisymmetric in its first pair `(Y,Z)` — each Leibniz term is,
pointwise. -/
theorem covariantDerivativeCurvatureFour_antisymm₁₂
    {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {X Y Z V U : Π x : M, TangentSpace I x}
    (hY : IsSmoothVectorField Y) (hZ : IsSmoothVectorField Z)
    (hV : IsSmoothVectorField V) (hU : IsSmoothVectorField U) (p : M) :
    covariantDerivativeCurvatureFour D X Y Z V U p
      = -covariantDerivativeCurvatureFour D X Z Y V U p := by
  have hfun : curvatureTensorFour D Z Y V U
      = fun q => (-1 : ℝ) * curvatureTensorFour D Y Z V U q := by
    funext q
    rw [curvatureTensorFour_antisymm_left D Z Y V U q]
    ring
  have hsm : MDifferentiableAt I 𝓘(ℝ) (curvatureTensorFour D Y Z V U) p :=
    ((contMDiff_curvatureTensorFour D hY hZ hV hU) p).mdifferentiableAt
      (by simp)
  have hdd : directionalDerivative X (curvatureTensorFour D Z Y V U) p
      = -directionalDerivative X (curvatureTensorFour D Y Z V U) p := by
    rw [hfun, directionalDerivative_const_smul hsm (-1) X]
    ring
  simp only [covariantDerivativeCurvatureFour_apply, hdd,
    curvatureTensorFour_antisymm_left D Y (D.toAffineConnection.covField X Z) V U p,
    curvatureTensorFour_antisymm_left D (D.toAffineConnection.covField X Y) Z V U p,
    curvatureTensorFour_antisymm_left D Y Z (D.toAffineConnection.covField X V) U p,
    curvatureTensorFour_antisymm_left D Y Z V (D.toAffineConnection.covField X U) p]
  ring

/-- `∇R` is antisymmetric in its last pair `(V,U)`. -/
theorem covariantDerivativeCurvatureFour_antisymm₃₄
    {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {X Y Z V U : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (hV : IsSmoothVectorField V)
    (hU : IsSmoothVectorField U) (p : M) :
    covariantDerivativeCurvatureFour D X Y Z V U p
      = -covariantDerivativeCurvatureFour D X Y Z U V p := by
  have hcY : IsSmoothVectorField (D.toAffineConnection.covField X Y) :=
    D.smooth_cov hX hY
  have hcZ : IsSmoothVectorField (D.toAffineConnection.covField X Z) :=
    D.smooth_cov hX hZ
  have hcV : IsSmoothVectorField (D.toAffineConnection.covField X V) :=
    D.smooth_cov hX hV
  have hcU : IsSmoothVectorField (D.toAffineConnection.covField X U) :=
    D.smooth_cov hX hU
  have hfun : curvatureTensorFour D Y Z U V
      = fun q => (-1 : ℝ) * curvatureTensorFour D Y Z V U q := by
    funext q
    rw [curvatureTensorFour_antisymm_right D hY hZ hU hV q]
    ring
  have hsm : MDifferentiableAt I 𝓘(ℝ) (curvatureTensorFour D Y Z V U) p :=
    ((contMDiff_curvatureTensorFour D hY hZ hV hU) p).mdifferentiableAt
      (by simp)
  have hdd : directionalDerivative X (curvatureTensorFour D Y Z U V) p
      = -directionalDerivative X (curvatureTensorFour D Y Z V U) p := by
    rw [hfun, directionalDerivative_const_smul hsm (-1) X]
    ring
  simp only [covariantDerivativeCurvatureFour_apply, hdd,
    curvatureTensorFour_antisymm_right D hcY hZ hU hV p,
    curvatureTensorFour_antisymm_right D hY hcZ hU hV p,
    curvatureTensorFour_antisymm_right D hY hZ hcU hV p,
    curvatureTensorFour_antisymm_right D hY hZ hU hcV p]
  ring

/-- `∇R` has the pair-swap symmetry `(∇_X R)(Y,Z,V,U) = (∇_X R)(V,U,Y,Z)`. -/
theorem covariantDerivativeCurvatureFour_pairSwap
    {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {X Y Z V U : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (hV : IsSmoothVectorField V)
    (hU : IsSmoothVectorField U) (p : M) :
    covariantDerivativeCurvatureFour D X Y Z V U p
      = covariantDerivativeCurvatureFour D X V U Y Z p := by
  have hcY : IsSmoothVectorField (D.toAffineConnection.covField X Y) :=
    D.smooth_cov hX hY
  have hcZ : IsSmoothVectorField (D.toAffineConnection.covField X Z) :=
    D.smooth_cov hX hZ
  have hcV : IsSmoothVectorField (D.toAffineConnection.covField X V) :=
    D.smooth_cov hX hV
  have hcU : IsSmoothVectorField (D.toAffineConnection.covField X U) :=
    D.smooth_cov hX hU
  have hfun : curvatureTensorFour D Y Z V U = curvatureTensorFour D V U Y Z := by
    funext q
    exact curvatureTensorFour_pairSwap D hY hZ hV hU q
  simp only [covariantDerivativeCurvatureFour_apply, hfun,
    curvatureTensorFour_pairSwap D hcY hZ hV hU p,
    curvatureTensorFour_pairSwap D hY hcZ hV hU p,
    curvatureTensorFour_pairSwap D hY hZ hcV hU p,
    curvatureTensorFour_pairSwap D hY hZ hV hcU p]
  ring

end PetersenLib
