import PetersenLib.Ch03.RicciCurvature
import PetersenLib.Ch04.ConformalWarped

/-!
# Petersen Ch. 3, §3.4 — Exercise 3.4.18: behaviour of curvature under scaling

**Math.** Petersen, *Riemannian Geometry* (3rd ed.), Exercise 3.4.18, p. 125.

Scaling `(M, g)` to `(M, λ²g)` (`λ ≠ 0`):

1. the Levi-Civita connection and the `(1,3)`-curvature tensor are **unchanged**
   (they are functions of the affine connection alone, not of `g`);
2. the sectional curvature `sec` and the scalar curvature `scal` are multiplied
   by `λ⁻²` (the curvature numerator scales like `g`, i.e. by `λ²`, while the
   bivector norm in the denominator scales like `g²`, i.e. by `λ⁴`);
3. the Ricci endomorphism (the `(1,1)`-Ricci tensor) is multiplied by `λ⁻²`
   (the metric–Riesz dual of the fixed `(0,2)`-Ricci form scales oppositely to
   `g`);
4. the Ricci `(0,2)`-tensor `Ric(v,w)` is **unchanged** (again a function of the
   affine connection alone).

We realise `(M, λ²g)` as the conformal change `conformalChangeOfMetric` with the
constant conformal factor `ψ ≡ |λ|`, so that `ψ² ≡ λ²`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.4, p. 125.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

namespace MetricScaling

/-- `x⁻² = (x²)⁻¹` (rewriting the `ℤ`-power as a `ℕ`-power). -/
private theorem zpow_neg_two (x : ℝ) : x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := by
  rw [zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]

/-- The core algebraic identity behind the `λ⁻²` scaling of the sectional
curvature: numerator scales by `l²`, denominator (a bivector norm) by `l⁴`. -/
private theorem scale_div (l a b : ℝ) (hl : l ≠ 0) :
    (l ^ 2 * a) / (l ^ 4 * b) = l ^ (-2 : ℤ) * (a / b) := by
  rw [zpow_neg_two]
  rcases eq_or_ne b 0 with hb | hb
  · simp [hb]
  · have hl2 : (l : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hl
    field_simp

section Helper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
/-- Constant-factor version of the directional-derivative scaling for the
*raw* directional derivative `dirTangent` used in `metric_compat`. -/
private theorem dirTangent_const_smul_fun {f : M → ℝ} {p : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f p) (c : ℝ) (v : TangentSpace I p) :
    dirTangent (fun q => c * f q) v = c * dirTangent f v := by
  have h1 : (fun q => c * f q) = c • f := rfl
  rw [dirTangent, dirTangent, h1]
  exact congrArg (fun L => L v) ((hf.hasMFDerivAt.const_smul c).mfderiv)

end Helper

end MetricScaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

open MetricScaling in
/-- **Math.** Petersen, Exercise 3.4.18 (p. 125). Scaling `(M, g)` to
`(M, λ²g)` with `λ ≠ 0` (realised as the conformal change with constant factor
`|λ|`): there is a Levi-Civita connection `D'` for `λ²g` whose underlying affine
connection and `(1,3)`-curvature tensor coincide with those of the given
Levi-Civita connection `D` for `g`; the sectional and scalar curvatures are
multiplied by `λ⁻²`; the Ricci endomorphism (the `(1,1)`-Ricci tensor) is
multiplied by `λ⁻²`; and the `(0,2)`-Ricci tensor is unchanged. -/
theorem exercise3_4_18
    {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    (lam : ℝ) (hlam : lam ≠ 0) :
    ∃ D' : RiemannianConnection I
        (conformalChangeOfMetric g (fun _ => |lam|) contMDiff_const
          (fun _ => abs_pos.mpr hlam)),
      D'.toAffineConnection = D.toAffineConnection ∧
      curvatureTensor D'.toAffineConnection = curvatureTensor D.toAffineConnection ∧
      (∀ (p : M) (v w : TangentSpace I p),
        sectionalCurvature D' p v w = lam ^ (-2 : ℤ) * sectionalCurvature D p v w) ∧
      (∀ p : M, scalarCurvature D' p = lam ^ (-2 : ℤ) * scalarCurvature D p) ∧
      (∀ (p : M) (v : TangentSpace I p),
        ricciEndomorphism D' p v = (lam ^ (-2 : ℤ)) • ricciEndomorphism D p v) ∧
      (∀ (p : M) (v w : TangentSpace I p),
        RicciCurvature D'.toAffineConnection p v w
          = RicciCurvature D.toAffineConnection p v w) := by
  set g' := conformalChangeOfMetric g (fun _ => |lam|) contMDiff_const
    (fun _ => abs_pos.mpr hlam) with hg'
  -- The rescaled Levi-Civita connection: same covariant derivative as `D`.
  let D' : RiemannianConnection I g' :=
    { D.toAffineConnection with
      torsion_free := D.torsion_free
      metric_compat := by
        intro X Y hX hY p v
        have hmdf : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun q => g.metricInner q (X q) (Y q)) p :=
          g.metricInner_raw_mdifferentiableAt (hX.mdifferentiableAt (by simp))
            (hY.mdifferentiableAt (by simp))
        simp only [hg', conformalChangeOfMetric_apply]
        rw [dirTangent_const_smul_fun hmdf, D.metric_compat hX hY p v, mul_add] }
  -- `g'.metricInner = |λ|² · g.metricInner`.
  have hinner : ∀ (p : M) (u w : TangentSpace I p),
      g'.metricInner p u w = |lam| ^ 2 * g.metricInner p u w := fun p u w => rfl
  -- `|λ|² = λ²`.
  have habs : |lam| ^ 2 = lam ^ 2 := sq_abs lam
  -- `λ⁻² · λ² = 1`.
  have hcancel : (lam : ℝ) ^ (-2 : ℤ) * |lam| ^ 2 = 1 := by
    rw [habs, zpow_neg_two]
    exact inv_mul_cancel₀ (pow_ne_zero 2 hlam)
  -- (3) Ricci endomorphism scales by `λ⁻²`.
  have hRicEnd : ∀ (p : M) (v : TangentSpace I p),
      ricciEndomorphism D' p v = (lam ^ (-2 : ℤ)) • ricciEndomorphism D p v := by
    intro p v
    refine (g'.metricInner_eq_iff_eq p _ _).mp fun Z => ?_
    rw [metricInner_ricciEndomorphism, g'.metricInner_smul_left, hinner,
      metricInner_ricciEndomorphism]
    show RicciCurvature D.toAffineConnection p v Z
      = lam ^ (-2 : ℤ) * (|lam| ^ 2 * RicciCurvature D.toAffineConnection p v Z)
    rw [← mul_assoc, hcancel, one_mul]
  -- (2)/(3) scalar curvature scales by `λ⁻²`.
  have hScal : ∀ p : M, scalarCurvature D' p = lam ^ (-2 : ℤ) * scalarCurvature D p := by
    intro p
    have hlin : ricciEndomorphismLinear D' p
        = (lam ^ (-2 : ℤ)) • ricciEndomorphismLinear D p := by
      ext v
      rw [LinearMap.smul_apply]
      exact hRicEnd p v
    show LinearMap.trace ℝ (TangentSpace I p) (ricciEndomorphismLinear D' p)
      = lam ^ (-2 : ℤ) * LinearMap.trace ℝ (TangentSpace I p) (ricciEndomorphismLinear D p)
    rw [hlin, map_smul, smul_eq_mul]
  -- (2) sectional curvature scales by `λ⁻²`.
  have hSec : ∀ (p : M) (v w : TangentSpace I p),
      sectionalCurvature D' p v w = lam ^ (-2 : ℤ) * sectionalCurvature D p v w := by
    intro p v w
    have hbiv : bivectorInnerProduct g' p v w v w
        = lam ^ 4 * bivectorInnerProduct g p v w v w := by
      simp only [bivectorInnerProduct, hinner, habs]
      ring
    show g'.metricInner p (directionalCurvatureOperator D'.toAffineConnection p v w) w
        / bivectorInnerProduct g' p v w v w
      = lam ^ (-2 : ℤ) *
        (g.metricInner p (directionalCurvatureOperator D.toAffineConnection p v w) w
          / bivectorInnerProduct g p v w v w)
    rw [hbiv, hinner, habs]
    exact scale_div lam _ _ hlam
  exact ⟨D', rfl, rfl, hSec, hScal, hRicEnd, fun p v w => rfl⟩

end PetersenLib
