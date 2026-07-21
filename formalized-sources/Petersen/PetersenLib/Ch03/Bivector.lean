import PetersenLib.Ch03.AlgebraicCurvatureForm
import PetersenLib.Foundations.RiemannianMetric

/-!
# Petersen Ch. 3, §3.1.2 — Bivectors

The inner product on bivectors `g(x∧y, v∧w) = g(x,v)g(y,w) − g(x,w)g(y,v)`
(`bivectorInnerProduct`), the interpretation of a bivector `x∧y` as the
skew-symmetric transformation `(x∧y)(v) = g(x,v)y − g(y,v)x`
(`bivectorSkewMap`), their compatibility
(`bivectorSkewMap_metricInner`), and the Jacobi identity
`(x∧y)(z) + (y∧z)(x) + (z∧x)(y) = 0` (`bivectorSkewMap_jacobi`).

The metric at a point is also packaged as a bilinear form
(`RiemannianMetric.metricBilin`), connecting the pointwise objects to the
abstract algebraic-curvature-form layer (`bivectorPairing`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.2.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The metric at a point, packaged as a bilinear form on the tangent space. -/
def RiemannianMetric.metricBilin (g : RiemannianMetric I M) (p : M) :
    LinearMap.BilinForm ℝ (TangentSpace I p) :=
  LinearMap.mk₂ ℝ (fun v w => g.metricInner p v w)
    (fun _ _ _ => g.metricInner_add_left ..)
    (fun _ _ _ => g.metricInner_smul_left ..)
    (fun _ _ _ => g.metricInner_add_right ..)
    (fun _ _ _ => g.metricInner_smul_right ..)

@[simp]
theorem RiemannianMetric.metricBilin_apply (g : RiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) : g.metricBilin p v w = g.metricInner p v w := rfl

/-- **Math.** The **inner product on bivectors** (Petersen §3.1.2): on
`Λ²T_pM`, the inner product making `{e_i ∧ e_j}_{i<j}` orthonormal for an
orthonormal basis `e` of `T_pM` is determined on decomposable bivectors by the
Gram determinant
`g(x∧y, v∧w) = g(x,v)g(y,w) − g(x,w)g(y,v)`. -/
def bivectorInnerProduct (g : RiemannianMetric I M) (p : M)
    (x y v w : TangentSpace I p) : ℝ :=
  g.metricInner p x v * g.metricInner p y w
    - g.metricInner p x w * g.metricInner p y v

theorem bivectorInnerProduct_eq_bivectorPairing (g : RiemannianMetric I M)
    (p : M) (x y v w : TangentSpace I p) :
    bivectorInnerProduct g p x y v w = bivectorPairing (g.metricBilin p) x y v w := rfl

/-- **Math.** A bivector `x ∧ y` interpreted as the **skew-symmetric
transformation** (Petersen §3.1.2)
`(x∧y)(v) = g(x,v)y − g(y,v)x` — a counter-clockwise 90° rotation on
`span{x,y}` when `x, y` are orthonormal. -/
def bivectorSkewMap (g : RiemannianMetric I M) (p : M)
    (x y v : TangentSpace I p) : TangentSpace I p :=
  g.metricInner p x v • y - g.metricInner p y v • x

/-- The compatibility `g((x∧y)(v), w) = g(x∧y, v∧w)` between the skew-map
interpretation and the bivector inner product (Petersen §3.1.2). -/
theorem bivectorSkewMap_metricInner (g : RiemannianMetric I M) (p : M)
    (x y v w : TangentSpace I p) :
    g.metricInner p (bivectorSkewMap g p x y v) w
      = bivectorInnerProduct g p x y v w := by
  rw [bivectorSkewMap, bivectorInnerProduct, g.metricInner_sub_left,
    g.metricInner_smul_left, g.metricInner_smul_left]
  ring

/-- **Math.** The **Jacobi identity for bivector maps** (Petersen §3.1.2):
`(x∧y)(z) + (y∧z)(x) + (z∧x)(y) = 0`. Expanding each term by the definition,
the sum groups as
`(g(x,z)−g(z,x))y + (g(y,x)−g(x,y))z + (g(z,y)−g(y,z))x = 0` by symmetry of
`g`. -/
theorem bivectorSkewMap_jacobi (g : RiemannianMetric I M) (p : M)
    (x y z : TangentSpace I p) :
    bivectorSkewMap g p x y z + bivectorSkewMap g p y z x
      + bivectorSkewMap g p z x y = 0 := by
  simp only [bivectorSkewMap]
  rw [g.metricInner_comm p x z, g.metricInner_comm p y x, g.metricInner_comm p z y]
  module

end PetersenLib
