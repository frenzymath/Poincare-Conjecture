import PetersenLib.Ch06.JacobiChartBridge
import PetersenLib.Ch06.JacobiLinearity

/-!
# Petersen Ch. 6, §6.1 — interval algebra for Jacobi fields

The local ODE and exponential-variation constructions produce
`IsJacobiFieldAlongOn`, rather than a solution on all of `ℝ`.  This module gives that
interval predicate the same elementary linear structure as the global predicate in
`JacobiLinearity.lean`, so local solutions can be restricted and combined before a
chart-cover gluing argument is available.
-/

open Set Bundle Manifold
open scoped Manifold Topology ContDiff Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** The zero field solves the Jacobi equation on every set. -/
theorem isJacobiFieldAlongOn_zero (g : RiemannianMetric I M) (c : ℝ → M) (s : Set ℝ) :
    IsJacobiFieldAlongOn (I := I) g c (fun t => (0 : TangentSpace I (c t))) s := by
  intro t _
  exact isJacobiFieldAlong_zero (I := I) g c t

/-- **Math.** A Jacobi field on `s` is a Jacobi field on every smaller time domain. -/
theorem IsJacobiFieldAlongOn.mono {g : RiemannianMetric I M} {c : ℝ → M}
    {J : ∀ t, TangentSpace I (c t)} {s s' : Set ℝ}
    (hJ : IsJacobiFieldAlongOn (I := I) g c J s) (hss' : s' ⊆ s) :
    IsJacobiFieldAlongOn (I := I) g c J s' :=
  fun t ht => hJ t (hss' ht)

/-- **Math.** The sum of two Jacobi fields is Jacobi on their common time domain.
The regularity hypotheses are exactly those needed by the global superposition lemma. -/
theorem isJacobiFieldAlongOn_add
    (g : RiemannianMetric I M) (c : ℝ → M) (s : Set ℝ)
    (V W : ∀ t, TangentSpace I (c t))
    (hV : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t)
    (hW : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t)
    (hV' : ∀ t, DifferentiableAt ℝ
      (chartFieldRep (I := I) c (c t) (fun u => derivAlongCurve (I := I) g c V u)) t)
    (hW' : ∀ t, DifferentiableAt ℝ
      (chartFieldRep (I := I) c (c t) (fun u => derivAlongCurve (I := I) g c W u)) t)
    (hVJ : IsJacobiFieldAlongOn (I := I) g c V s)
    (hWJ : IsJacobiFieldAlongOn (I := I) g c W s) :
    IsJacobiFieldAlongOn (I := I) g c (fun t => V t + W t) s := by
  intro t ht
  rw [jacobiEquation_add (I := I) g c V W hV hW hV' hW' t, hVJ t ht, hWJ t ht, add_zero]

/-- **Math.** A constant scalar multiple of a Jacobi field is Jacobi on the same domain. -/
theorem isJacobiFieldAlongOn_const_smul
    (g : RiemannianMetric I M) (c : ℝ → M) (s : Set ℝ) (r : ℝ)
    (V : ∀ t, TangentSpace I (c t))
    (hV : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t)
    (hV' : ∀ t, DifferentiableAt ℝ
      (chartFieldRep (I := I) c (c t) (fun u => derivAlongCurve (I := I) g c V u)) t)
    (hVJ : IsJacobiFieldAlongOn (I := I) g c V s) :
    IsJacobiFieldAlongOn (I := I) g c (fun t => r • V t) s := by
  intro t ht
  rw [jacobiEquation_const_smul (I := I) g c r V hV hV' t, hVJ t ht, smul_zero]

end PetersenLib

end
