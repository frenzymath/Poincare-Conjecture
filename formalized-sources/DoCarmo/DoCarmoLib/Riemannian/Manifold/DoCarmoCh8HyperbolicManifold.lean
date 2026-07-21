import DoCarmoLib.Riemannian.Manifold.EuclideanOpens
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh8Hyperbolic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Hyperbolic space `Hⁿ` as a Riemannian manifold (do Carmo Ch. 8 §3)

do Carmo's hyperbolic space is the open upper half-space
`Hⁿ = {x ∈ ℝⁿ : xₙ > 0}` equipped with the metric `gᵢⱼ = δᵢⱼ / xₙ²`, which is
*conformal* to the ambient Euclidean metric with conformal factor `1/xₙ²`.

This file builds `Hⁿ` as a genuine DoCarmoLib `RiemannianMetric`, the central
object of the chapter (previously the §3 material lived only as a
coordinate/algebraic curvature computation in `DoCarmoCh8Hyperbolic.lean`,
untied to any actual manifold).

* `opensConformalMetric` — the reusable constructor: a smooth positive function
  `φ` on an open subset `s ⊆ F` of a Euclidean space scales the restricted
  Euclidean metric to `⟪v, w⟫ ↦ φ · ⟪v, w⟫`. Its smoothness is inherited from
  the flat metric (`opensEuclideanMetric`) via `ContMDiff.smul_section`, and the
  metric ball `{v | φ‖v‖² < 1}` is a genuine Euclidean ball, so
  von-Neumann-boundedness is immediate.
* `hyperbolicMetric` — `opensConformalMetric` on the half-space
  `upperHalfSpace e = {x : xₑ > 0}` with `φ(x) = 1/xₑ²`, i.e. do Carmo's metric
  `gᵢⱼ = δᵢⱼ/xₑ²`.
* `hyperbolicMetric_apply` — the metric inner product is
  `⟪v, w⟫_g = (1/xₑ²)·⟪v, w⟫`, do Carmo's `gᵢⱼ = δᵢⱼ/xₑ²` read on tangent vectors.

Reference: do Carmo, *Riemannian Geometry*, Ch. 8 §3, eq. (1).
-/

open scoped RealInnerProductSpace Manifold ContDiff
open Bundle TopologicalSpace

noncomputable section

namespace Riemannian

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-! ## The conformal rescaling of the Euclidean metric on an open subset -/

/-- **Math.** do Carmo Ch. 8 §3 (conformal metric). Given an open subset `s ⊆ F`
of a (complete real) inner-product space and a smooth positive function `φ : ↥s → ℝ`,
the pointwise rescaling `⟪v, w⟫ ↦ φ(q)·⟪v, w⟫` of the ambient Euclidean metric is
a Riemannian metric on `↥s` — the conformal metric with conformal factor `φ`.

Smoothness of the metric section is inherited from the flat metric
`opensEuclideanMetric` through `ContMDiff.smul_section`; positive-definiteness and
von-Neumann boundedness follow because the metric ball is the Euclidean ball of
radius `√(1/φ)`. -/
def opensConformalMetric (s : Opens F) (φ : ↥s → ℝ)
    (hφ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ φ) (hpos : ∀ q, 0 < φ q) :
    RiemannianMetric 𝓘(ℝ, F) ↥s where
  inner q := φ q • (opensEuclideanMetric s).inner q
  symm q v w := by
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    congr 1
    exact (opensEuclideanMetric s).symm q v w
  pos q v hv := by
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_pos (hpos q) ((opensEuclideanMetric s).pos q v hv)
  isVonNBounded q := by
    have hφq : 0 < φ q := hpos q
    have hE : ∀ a b : F, (opensEuclideanMetric s).inner q a b = ⟪a, b⟫ :=
      fun _ _ => rfl
    have hset : {v : F | (φ q • (opensEuclideanMetric s).inner q) v v < 1}
        = Metric.ball (0 : F) (Real.sqrt (1 / φ q)) := by
      ext v
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hE,
        Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right,
        Real.lt_sqrt (norm_nonneg v), real_inner_self_eq_norm_sq]
      rw [lt_div_iff₀ hφq, mul_comm]
    exact hset ▸ NormedSpace.isVonNBounded_ball ℝ F _
  contMDiff := ContMDiff.smul_section hφ (opensEuclideanMetric s).contMDiff

omit [CompleteSpace F] in
@[simp] theorem opensConformalMetric_apply (s : Opens F) (φ : ↥s → ℝ)
    (hφ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ φ) (hpos : ∀ q, 0 < φ q)
    (q : ↥s) (v w : F) :
    (opensConformalMetric s φ hφ hpos).metricInner q v w = φ q * ⟪v, w⟫ := by
  show (φ q • (opensEuclideanMetric s).inner q) v w = φ q * _
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

end Riemannian

/-! ## Hyperbolic space `Hⁿ` -/

namespace Riemannian.Hyperbolic

open Riemannian

variable {n : ℕ}

/-- **Math.** The open upper half-space `Hⁿ = {x ∈ ℝⁿ : xₑ > 0}`, distinguished
coordinate `e` (do Carmo's last coordinate `xₙ`). -/
def upperHalfSpace (e : Fin n) : Opens (EuclideanSpace ℝ (Fin n)) where
  carrier := {x | 0 < x e}
  is_open' := by
    have : Continuous fun x : EuclideanSpace ℝ (Fin n) => x e := by
      simpa using (EuclideanSpace.proj (𝕜 := ℝ) e).continuous
    exact isOpen_lt continuous_const this

@[simp] theorem mem_upperHalfSpace (e : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ upperHalfSpace e ↔ 0 < x e := Iff.rfl

/-- **Math.** On the half-space the distinguished coordinate is positive. -/
theorem coord_pos (e : Fin n) (q : ↥(upperHalfSpace e)) :
    0 < (q : EuclideanSpace ℝ (Fin n)) e := q.property

/-- **Math.** The conformal factor `φ(x) = 1/xₑ²` of do Carmo's hyperbolic metric
`gᵢⱼ = δᵢⱼ/xₑ²`. -/
def hyperbolicConformalFactor (e : Fin n) (q : ↥(upperHalfSpace e)) : ℝ :=
  ((q.val e) ^ 2)⁻¹

/-- **Math.** The conformal factor `1/xₑ²` is positive. -/
theorem hyperbolicConformalFactor_pos (e : Fin n) (q : ↥(upperHalfSpace e)) :
    0 < hyperbolicConformalFactor e q := by
  have := coord_pos e q
  unfold hyperbolicConformalFactor
  positivity

/-- **Math.** The coordinate map `q ↦ xₑ` is smooth on the half-space. -/
theorem contMDiff_coord (e : Fin n) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞
      (fun q : ↥(upperHalfSpace e) => (q : EuclideanSpace ℝ (Fin n)) e) :=
  (EuclideanSpace.proj (𝕜 := ℝ) e).contMDiff.comp contMDiff_subtype_val_opens

/-- **Math.** The conformal factor `1/xₑ²` is a smooth function on the half-space
(it is nonvanishing there, since `xₑ > 0`). -/
theorem contMDiff_hyperbolicConformalFactor (e : Fin n) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞
      (hyperbolicConformalFactor e) := by
  intro q
  refine ContMDiffAt.inv₀ (((contMDiff_coord e) q).pow 2) ?_
  have := coord_pos e q
  positivity

/-- **Math.** do Carmo Ch. 8 §3, eq. (1): **hyperbolic space `Hⁿ`**, the
half-space `{xₑ > 0} ⊆ ℝⁿ` with the metric `gᵢⱼ = δᵢⱼ/xₑ²`, packaged as an
DoCarmoLib Riemannian manifold (the conformal rescaling of the ambient Euclidean
metric by `1/xₑ²`). -/
def hyperbolicMetric (e : Fin n) :
    RiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ↥(upperHalfSpace e) :=
  opensConformalMetric (upperHalfSpace e) (hyperbolicConformalFactor e)
    (contMDiff_hyperbolicConformalFactor e) (hyperbolicConformalFactor_pos e)

/-- **Math.** do Carmo Ch. 8 §3, eq. (1): the hyperbolic metric read on tangent
vectors, `⟪v, w⟫_g = (1/xₑ²)·⟪v, w⟫` — his `gᵢⱼ = δᵢⱼ/xₑ²` (the coordinate frame
of `ℝⁿ` is orthonormal for the ambient `⟪·,·⟫`, so on basis vectors this is
`δᵢⱼ/xₑ²`). -/
@[simp] theorem hyperbolicMetric_apply (e : Fin n) (q : ↥(upperHalfSpace e))
    (v w : EuclideanSpace ℝ (Fin n)) :
    (hyperbolicMetric e).metricInner q v w = ((q.val e) ^ 2)⁻¹ * ⟪v, w⟫ := by
  rw [hyperbolicMetric, opensConformalMetric_apply]
  rfl

/-- **Math.** do Carmo Ch. 8 §3, eq. (1) in coordinates: the Gram matrix of the
hyperbolic metric on the standard orthonormal coordinate frame
`∂/∂x_i = EuclideanSpace.basisFun i` is exactly do Carmo's `g_{ij} = δ_{ij}/x_e²`. -/
theorem hyperbolicMetric_gram (e : Fin n) (q : ↥(upperHalfSpace e)) (i j : Fin n) :
    (hyperbolicMetric e).metricInner q
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
      = ((q.val e) ^ 2)⁻¹ * (if i = j then 1 else 0) := by
  rw [hyperbolicMetric_apply]
  congr 1
  have ho := (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal
  rw [orthonormal_iff_ite] at ho
  exact ho i j

end Riemannian.Hyperbolic

end
