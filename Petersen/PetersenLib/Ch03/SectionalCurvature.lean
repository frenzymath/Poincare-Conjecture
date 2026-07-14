import PetersenLib.Ch03.CurvaturePointwise

/-!
# Petersen Ch. 3, §3.1.3 — Sectional curvature

The directional (tidal force) curvature operator `R_v(w) = R(w,v)v`
(`directionalCurvatureOperator`), the sectional curvature
`sec(v,w) = g(R(w,v)v, w) / g(v∧w, v∧w)` (`sectionalCurvature`), and constant
curvature (`HasConstantCurvature`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.3.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** The **directional (tidal force) curvature operator**
(Petersen §3.1.3): for `v ∈ T_pM`, the operator `R_v(w) = R(w,v)v : T_pM → T_pM`.
It is self-adjoint and has `v` as a zero eigenvector, by the symmetries of the
curvature tensor. -/
def directionalCurvatureOperator (D : AffineConnection I M) (p : M)
    (v w : TangentSpace I p) : TangentSpace I p :=
  curvatureTensorAt D p w v v

/-- `R_v(v) = 0`: the direction itself is a zero eigenvector (antisymmetry). -/
theorem directionalCurvatureOperator_self (D : AffineConnection I M) (p : M)
    (v : TangentSpace I p) : directionalCurvatureOperator D p v v = 0 := by
  have h := curvatureTensorAt_antisymm_first D p v v v
  have h2 : (2 : ℝ) • curvatureTensorAt D p v v v = 0 := by
    rw [two_smul]
    linear_combination (norm := module) h
  have h3 := congrArg (fun t => (1 / 2 : ℝ) • t) h2
  simpa [smul_smul, directionalCurvatureOperator] using h3

/-- **Math.** The **sectional curvature** (Petersen §3.1.3): the normalized
biquadratic form
`sec(v,w) = g(R_v(w), w) / (g(v,v)g(w,w) − g(v,w)²) = g(R(w,v)v, w) / g(v∧w, v∧w)`,
depending only on the plane spanned by `v, w`. -/
def sectionalCurvature {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (p : M) (v w : TangentSpace I p) : ℝ :=
  g.metricInner p (directionalCurvatureOperator D.toAffineConnection p v w) w
    / bivectorInnerProduct g p v w v w

/-- The sectional curvature through the pointwise `(0,4)`-curvature tensor. -/
theorem sectionalCurvature_eq_curvatureTensorFourAt {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (p : M) (v w : TangentSpace I p) :
    sectionalCurvature D p v w
      = curvatureTensorFourAt D p w v v w / bivectorInnerProduct g p v w v w :=
  rfl

/-- **Math.** `(M,g)` has **constant curvature** `k` (Petersen §3.1.3):
every 2-plane at every point has sectional curvature `k`. By Riemann's
proposition this is equivalent to the other three pointwise conditions
holding with the same `k` at every point. -/
def HasConstantCurvature {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (k : ℝ) : Prop :=
  ∀ (p : M) (v w : TangentSpace I p), LinearIndependent ℝ ![v, w] →
    sectionalCurvature D p v w = k

end PetersenLib
