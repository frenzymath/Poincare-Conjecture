import PetersenLib.Ch06.HessianF0PosDef

/-!
# Petersen Ch. 6, §6.2 — the analytic no-second-zero implication

For a Jacobi field `J` with `J 0 = 0` on a manifold with nonpositive
sectional curvature, the scalar function `g(J, J')` is monotone.  The existing
strict Hessian estimate says that it is positive whenever `J` is nonzero at a
positive time.  Consequently, if `J` also vanishes at a later endpoint `b`, it
must vanish throughout `[0, b]`.

This is the analytic no-conjugate-point implication used in the proof of
Cartan--Hadamard.  It does not assert nonsingularity of the global exponential
map: that conclusion additionally needs an intrinsic differential-of-exp
identification and global Jacobi-field data along arbitrary radial geodesics.
-/

open Set Filter Bundle Manifold
open scoped Manifold Topology ContDiff Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** A Jacobi field in nonpositive sectional curvature which vanishes
at both endpoints `0` and `b` vanishes throughout `Icc 0 b`.

The conclusion is intentionally an along-curve statement.  In particular, it
does not identify the field with the differential of the intrinsic exponential
map or claim global nonsingularity of that map. -/
theorem jacobiField_eq_zero_on_Icc_of_endpoints_eq_zero_nonpositiveCurvature
    (g : RiemannianMetric I M) {c : ℝ → M}
    {J : ∀ t, TangentSpace I (c t)} (hJ : IsJacobiFieldAlong g c J)
    {b : ℝ} (hsec : HasSecBoundedAbove g.leviCivita 0)
    (hJ0 : J 0 = 0) (hJb : J b = 0)
    (hc : ∀ t, ContinuousAt c t)
    (hu : ∀ t, DifferentiableAt ℝ (fun τ => extChartAt I (c t) (c τ)) t)
    (hJd : ∀ t, DifferentiableAt ℝ (chartFieldRep c (c t) J) t)
    (hDJd : ∀ t, DifferentiableAt ℝ
      (chartFieldRep c (c t) (derivAlongCurve g c J)) t)
    (hG : ∀ t, ∀ i j, DifferentiableAt ℝ (chartGramOnE g (c t) i j)
      (extChartAt I (c t) (c t))) :
    Set.EqOn J 0 (Icc 0 b) := by
  let phi : ℝ → ℝ := fun t =>
    g.metricInner (c t) (J t) (derivAlongCurve g c J t)
  have hphiDeriv : ∀ s, HasDerivAt phi
      (g.metricInner (c s) (derivAlongCurve g c J s) (derivAlongCurve g c J s)
        - g.metricInner (c s)
            (curvatureTensorAt (g.leviCivita).toAffineConnection (c s)
              (J s) (curveVelocity c s) (curveVelocity c s)) (J s)) s := by
    intro s
    exact jacobiField_hasDerivAt_inner_deriv g hJ s hc hu hJd hDJd hG
  have hnonneg : ∀ s,
      0 ≤ g.metricInner (c s) (derivAlongCurve g c J s) (derivAlongCurve g c J s)
        - g.metricInner (c s)
            (curvatureTensorAt (g.leviCivita).toAffineConnection (c s)
              (J s) (curveVelocity c s) (curveVelocity c s)) (J s) := by
    intro s
    have hmetric := g.metricInner_self_nonneg (c s) (derivAlongCurve g c J s)
    have hcurv := curvatureTerm_nonpos_of_secBoundedAbove_zero g hsec J s
    linarith
  have hmono : Monotone phi := by
    apply monotone_of_deriv_nonneg (fun x => (hphiDeriv x).differentiableAt)
    intro x
    rw [(hphiDeriv x).deriv]
    exact hnonneg x
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    exact hJ0
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  by_contra hJt
  have hpos := hess_f0_posDef_nonpositiveCurvature g hJ htpos.le hsec hJ0 hJt
    hc hu hJd hDJd hG
  have hle : phi t ≤ phi b := hmono ht.2
  rw [show phi t = g.metricInner (c t) (J t) (derivAlongCurve g c J t) by rfl,
    g.metricInner_comm (c t) (J t) (derivAlongCurve g c J t)] at hle
  rw [show phi b = g.metricInner (c b) (J b) (derivAlongCurve g c J b) by rfl,
    hJb, g.metricInner_zero_left] at hle
  linarith

/-- **Math.** A Jacobi field in nonpositive sectional curvature which is
nonzero somewhere on `Icc 0 b` cannot vanish at the right endpoint `b`.

This is the direct no-second-zero corollary of
`jacobiField_eq_zero_on_Icc_of_endpoints_eq_zero_nonpositiveCurvature`. -/
theorem jacobiField_endpoint_ne_zero_nonpositiveCurvature
    (g : RiemannianMetric I M) {c : ℝ → M}
    {J : ∀ t, TangentSpace I (c t)} (hJ : IsJacobiFieldAlong g c J)
    {b : ℝ} (hsec : HasSecBoundedAbove g.leviCivita 0)
    (hJ0 : J 0 = 0)
    (hc : ∀ t, ContinuousAt c t)
    (hu : ∀ t, DifferentiableAt ℝ (fun τ => extChartAt I (c t) (c τ)) t)
    (hJd : ∀ t, DifferentiableAt ℝ (chartFieldRep c (c t) J) t)
    (hDJd : ∀ t, DifferentiableAt ℝ
      (chartFieldRep c (c t) (derivAlongCurve g c J)) t)
    (hG : ∀ t, ∀ i j, DifferentiableAt ℝ (chartGramOnE g (c t) i j)
      (extChartAt I (c t) (c t)))
    (hnontrivial : ∃ t ∈ Icc 0 b, J t ≠ 0) :
    J b ≠ 0 := by
  intro hJb
  obtain ⟨t, ht, hJt⟩ := hnontrivial
  exact hJt
    (jacobiField_eq_zero_on_Icc_of_endpoints_eq_zero_nonpositiveCurvature
      g hJ hsec hJ0 hJb hc hu hJd hDJd hG ht)

end PetersenLib

end
