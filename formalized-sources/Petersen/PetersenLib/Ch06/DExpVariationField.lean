import PetersenLib.Ch06.DExpChainRule
import PetersenLib.Ch06.VariationTransfers

/-!
# Petersen Ch. 6, §6.1 — identifying the exponential variation field with `D exp`

`DExpChainRule.lean` proves the fixed-chart calculus identity.  The tangent-valued
variation field is read at the moving foot, however, so Petersen's actual formula also
needs the existing chart-transfer dictionary.  This file composes the two facts on an
explicit open slab.  The slab hypotheses are retained: they are the same local normal-ball
conditions used by `jacobiField_dexp_relation` and do not imply a global differential
isomorphism for `exp_p`.
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
  [T2Space (TangentBundle I M)]

/-- **Math.** On a charted slab, the tangent-valued variation field of
`s,t ↦ exp_p(t (v+s w))` is the chart transport of `D exp_p|_{tv}(t w)`.

The derivative certificate is stated for the chart reading of `exp_p`; `hsrc` and `hd`
are the local source and differentiability conditions needed by the moving-foot transfer
lemma.  This is the precise local form of Petersen's displayed `J(t)=D exp_p(tJ(0))`
identity. -/
theorem expVariationField_eq_tangentCoordChange_dexp
    (g : RiemannianMetric I M) (p : M) (v w : E) (t : ℝ) (D : E →L[ℝ] E)
    (δ a b : ℝ) (hδ : 0 < δ) (ht : t ∈ Ioo a b)
    (hD : HasFDerivAt
      (fun z : E => extChartAt I p
        (expMap (I := I) g p (z : TangentSpace I p))) D (t • v))
    (hsrc : ∀ q ∈ Ioo (-δ) δ ×ˢ Ioo a b,
      expMap (I := I) g p
        ((q.2 • (v + q.1 • w) : E) : TangentSpace I p) ∈ (extChartAt I p).source)
    (hd : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => extChartAt I p
        (expMap (I := I) g p
          ((q.2 • (v + q.1 • w) : E) : TangentSpace I p))) (0, t)) :
    variationField (I := I) (fun s τ : ℝ =>
      expMap (I := I) g p ((τ • (v + s • w) : E) : TangentSpace I p)) t =
      tangentCoordChange I p
        (expMap (I := I) g p ((t • v : E) : TangentSpace I p))
        (expMap (I := I) g p ((t • v : E) : TangentSpace I p))
        (D (t • w)) := by
  let f : ℝ → ℝ → M := fun s τ : ℝ =>
    expMap (I := I) g p ((τ • (v + s • w) : E) : TangentSpace I p)
  let c : ℝ × ℝ → E := fun q : ℝ × ℝ => extChartAt I p (f q.1 q.2)
  have hcdef : c = fun q : ℝ × ℝ => extChartAt I p (f q.1 q.2) := rfl
  have hsrc' : ∀ q ∈ Ioo (-δ) δ ×ˢ Ioo a b,
      Function.uncurry f q ∈ (extChartAt I p).source := by
    intro q hq
    change expMap (I := I) g p
        ((q.2 • (v + q.1 • w) : E) : TangentSpace I p) ∈ (extChartAt I p).source
    exact hsrc q hq
  have hd' : DifferentiableAt ℝ c (0, t) := by
    simpa [c, f] using hd
  have hvf := variationField_eq_tangentCoordChange (I := I) p hδ ht hcdef hd' hsrc'
  have hslice := Jacobi.hasDerivAt_comp_fst hd.hasFDerivAt
  have hrad := expChart_radialVariation_deriv_eq (I := I) g p v w t D hD
  have hderiv : fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ) = D (t • w) := by
    calc
      fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)
          = deriv (fun s : ℝ => c (s, t)) 0 := hslice.deriv.symm
      _ = D (t • w) := by simpa [c, f] using hrad
  rw [hvf, hderiv]
  simp [f]

end PetersenLib
