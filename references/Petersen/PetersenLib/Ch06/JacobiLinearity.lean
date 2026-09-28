import PetersenLib.Ch06.JacobiFields

/-!
# Petersen Ch. 6, §6.1 — linearity of the Jacobi equation

The Jacobi equation is a linear second-order equation, but the local definition of
`derivAlongCurve` uses the two-sided `deriv` and therefore returns `0` off the
differentiability locus.  Consequently, the useful superposition statements must
carry the chart-field differentiability hypotheses needed by the two applications of
`derivAlongCurve_add`/`derivAlongCurve_smul_fun`.

This file is support infrastructure for the Jacobi-field nodes.  It does not claim an
existence theorem for solutions of the ODE; it only records the algebraic
superposition law in a form that can be consumed by later comparison arguments.
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

/-- The first covariant derivative of a pointwise sum, as a function of time.

The hypothesis is stated for every time because the result is itself a function equality;
this is exactly the regularity needed by the outer derivative in the Jacobi equation. -/
theorem derivAlongCurve_add_fun
    (g : RiemannianMetric I M) (c : ℝ → M)
    (V W : ∀ t, TangentSpace I (c t))
    (hV : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t)
    (hW : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t) :
    (fun t => derivAlongCurve (I := I) g c (fun s => V s + W s) t) =
      (fun t => derivAlongCurve (I := I) g c V t +
        derivAlongCurve (I := I) g c W t) := by
  funext t
  exact derivAlongCurve_add (I := I) g c V W (hV t) (hW t)

/-- The first covariant derivative of a constant scalar multiple, as a function of time. -/
theorem derivAlongCurve_const_smul_fun
    (g : RiemannianMetric I M) (c : ℝ → M) (r : ℝ)
    (V : ∀ t, TangentSpace I (c t))
    (hV : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t) :
    (fun t => derivAlongCurve (I := I) g c (fun s => r • V s) t) =
      (fun t => r • derivAlongCurve (I := I) g c V t) := by
  funext t
  simpa using
    (derivAlongCurve_smul_fun (I := I) g c (fun _ : ℝ => r) V
      (t := t) (differentiableAt_const r) (hV t))

/-- **Math.** The pointwise Jacobi operator is additive in the field.

This is the local algebraic form of superposition.  The two regularity assumptions on
`V` and `W`, and the two assumptions on their first covariant derivatives, are explicit
because `derivAlongCurve` is defined using `deriv` (which is junk off its differentiability
locus). -/
theorem jacobiEquation_add
    (g : RiemannianMetric I M) (c : ℝ → M)
    (V W : ∀ t, TangentSpace I (c t))
    (hV : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t)
    (hW : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t)
    (hV' : ∀ t, DifferentiableAt ℝ
      (chartFieldRep (I := I) c (c t)
        (fun s => derivAlongCurve (I := I) g c V s)) t)
    (hW' : ∀ t, DifferentiableAt ℝ
      (chartFieldRep (I := I) c (c t)
        (fun s => derivAlongCurve (I := I) g c W s)) t)
    (t : ℝ) :
    jacobiEquation (I := I) g c (fun s => V s + W s) t =
      jacobiEquation (I := I) g c V t + jacobiEquation (I := I) g c W t := by
  rw [jacobiEquation_def]
  have hfirst := derivAlongCurve_add_fun (I := I) g c V W hV hW
  have hsecond := derivAlongCurve_add (I := I) g c
    (fun s => derivAlongCurve (I := I) g c V s)
    (fun s => derivAlongCurve (I := I) g c W s)
    (hV' t) (hW' t)
  rw [hfirst, hsecond, curvatureTensorAt_add_first]
  simp only [jacobiEquation_def]
  abel

/-- **Math.** Constant scalar multiples of Jacobi fields are Jacobi fields.

This is the scalar half of the same superposition law, with explicit regularity for the
field and its first covariant derivative. -/
theorem jacobiEquation_const_smul
    (g : RiemannianMetric I M) (c : ℝ → M) (r : ℝ)
    (V : ∀ t, TangentSpace I (c t))
    (hV : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t)
    (hV' : ∀ t, DifferentiableAt ℝ
      (chartFieldRep (I := I) c (c t)
        (fun s => derivAlongCurve (I := I) g c V s)) t)
    (t : ℝ) :
    jacobiEquation (I := I) g c (fun s => r • V s) t =
      r • jacobiEquation (I := I) g c V t := by
  rw [jacobiEquation_def]
  have hfirst := derivAlongCurve_const_smul_fun (I := I) g c r V hV
  have hsecond := derivAlongCurve_smul_fun (I := I) g c (fun _ : ℝ => r)
    (fun s => derivAlongCurve (I := I) g c V s) (t := t)
    (differentiableAt_const r) (hV' t)
  rw [hfirst, hsecond, curvatureTensorAt_smul_first]
  simp only [jacobiEquation_def]
  simp [deriv_const]

/-- **Math.** Superposition for along-curve Jacobi fields, under the regularity needed by
`derivAlongCurve`. -/
theorem isJacobiFieldAlong_add
    (g : RiemannianMetric I M) (c : ℝ → M)
    (V W : ∀ t, TangentSpace I (c t))
    (hV : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t)
    (hW : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t)
    (hV' : ∀ t, DifferentiableAt ℝ
      (chartFieldRep (I := I) c (c t)
        (fun s => derivAlongCurve (I := I) g c V s)) t)
    (hW' : ∀ t, DifferentiableAt ℝ
      (chartFieldRep (I := I) c (c t)
        (fun s => derivAlongCurve (I := I) g c W s)) t)
    (hVJ : IsJacobiFieldAlong (I := I) g c V)
    (hWJ : IsJacobiFieldAlong (I := I) g c W) :
    IsJacobiFieldAlong (I := I) g c (fun s => V s + W s) := by
  intro t
  rw [jacobiEquation_add (I := I) g c V W hV hW hV' hW' t, hVJ t, hWJ t,
    add_zero]

/-- **Math.** Constant scalar multiples of along-curve Jacobi fields are Jacobi fields. -/
theorem isJacobiFieldAlong_const_smul
    (g : RiemannianMetric I M) (c : ℝ → M) (r : ℝ)
    (V : ∀ t, TangentSpace I (c t))
    (hV : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t)
    (hV' : ∀ t, DifferentiableAt ℝ
      (chartFieldRep (I := I) c (c t)
        (fun s => derivAlongCurve (I := I) g c V s)) t)
    (hVJ : IsJacobiFieldAlong (I := I) g c V) :
    IsJacobiFieldAlong (I := I) g c (fun s => r • V s) := by
  intro t
  rw [jacobiEquation_const_smul (I := I) g c r V hV hV' t, hVJ t, smul_zero]

end PetersenLib

end
