import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.22 (Christoffel symbols of an induced metric)

For a parametrized submanifold `M^n ⊂ ℝ^{n+m}`, `x ↦ u(x)`, with the induced
(pullback) metric, Petersen asks to show

* `g_{ij} = ∑_s u^s_i u^s_j`, and
* `Γ_{ij,k} = ∑_s u^s_k u^s_{ij}`,

where `u^s_i = ∂u^s/∂x^i` and `u^s_{ij} = ∂²u^s/(∂x^i ∂x^j)`, and `Γ_{ij,k}` is
the Christoffel symbol of the first kind of the induced metric.

We formalize this in the honest coordinate form of the exercise: the ambient
manifold and its immersion bundle are not needed — the entire content is a
statement about the parametrization `u : E → F` (`F` a real inner product space,
playing the role of `ℝ^{n+m}`) and its first and second derivatives.  Writing
`Du_x = fderiv ℝ u x` for the differential and `D²u_x = fderiv ℝ (fderiv ℝ u) x`
for the (symmetric) second derivative:

* the induced metric is `g_x(v,w) = ⟪Du_x v, Du_x w⟫`
  (`inducedMetric`); in coordinates `g_{ij} = ∑_s u^s_i u^s_j`;
* the first-kind Christoffel symbol
  `Γ_x(v,w,z) = ½(D_v g(w,z) + D_w g(v,z) − D_z g(v,w))`
  (`inducedChristoffelFirst`) equals `⟪D²u_x(v,w), Du_x z⟫`
  (`inducedChristoffelFirst_eq`); in coordinates `Γ_{ij,k} = ∑_s u^s_{ij} u^s_k`.

The proof is the classical one: differentiate the inner products by the Leibniz
rule (`fderiv_inner_apply`), differentiate `y ↦ Du_y v` by `fderiv_clm_apply`,
and cancel four of the six resulting inner products using the symmetry of the
second derivative (`IsSymmSndFDerivAt`); the surviving two combine to
`2⟪D²u_x(v,w), Du_x z⟫`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercise 22.
-/

open scoped RealInnerProductSpace ContDiff

namespace PetersenLib

section InducedMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Math.** The components of the metric induced on a parametrized submanifold
by a parametrization `u : E → F`: `g_x(v, w) = ⟪Du_x v, Du_x w⟫`, the pullback
of the ambient inner product along the differential `Du_x = fderiv ℝ u x`.  In
coordinates `g_{ij} = ∑_s u^s_i u^s_j`. -/
noncomputable def inducedMetric (u : E → F) (x : E) (v w : E) : ℝ :=
  ⟪fderiv ℝ u x v, fderiv ℝ u x w⟫

/-- **Math.** The Christoffel symbol of the first kind of the induced metric,
`Γ_x(v, w, z) = ½(D_v g(w,z) + D_w g(v,z) − D_z g(v,w))`, where `D_v` is the
directional derivative in `x`. -/
noncomputable def inducedChristoffelFirst (u : E → F) (x : E) (v w z : E) : ℝ :=
  (1 / 2 : ℝ) *
    (fderiv ℝ (fun y => inducedMetric u y w z) x v
      + fderiv ℝ (fun y => inducedMetric u y v z) x w
      - fderiv ℝ (fun y => inducedMetric u y v w) x z)

variable {u : E → F} {x : E}

/-- **Eng.** The directional derivative of a metric component, by the Leibniz
rule for the inner product together with the derivative of `y ↦ Du_y v`
(`fderiv_clm_apply`): `D_z g(v,w) = ⟪Du_x v, D²u_x(z,w)⟫ + ⟪D²u_x(z,v), Du_x w⟫`. -/
theorem fderiv_inducedMetric (hu : ContDiff ℝ ∞ u) (v w z : E) :
    fderiv ℝ (fun y => inducedMetric u y v w) x z
      = ⟪fderiv ℝ u x v, fderiv ℝ (fderiv ℝ u) x z w⟫
        + ⟪fderiv ℝ (fderiv ℝ u) x z v, fderiv ℝ u x w⟫ := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    ((hu.fderiv_right (m := 1) (by norm_cast)).differentiable one_ne_zero).differentiableAt
  -- differentiability of `y ↦ Du_y v` and `y ↦ Du_y w`
  have hd1 : DifferentiableAt ℝ (fun y => fderiv ℝ u y v) x :=
    hfd.clm_apply (differentiableAt_const v)
  have hd2 : DifferentiableAt ℝ (fun y => fderiv ℝ u y w) x :=
    hfd.clm_apply (differentiableAt_const w)
  -- the two "apply a constant" derivatives
  have hclm : ∀ a : E, fderiv ℝ (fun y => fderiv ℝ u y a) x z
      = fderiv ℝ (fderiv ℝ u) x z a := by
    intro a
    rw [fderiv_clm_apply hfd (differentiableAt_const a)]
    simp
  calc fderiv ℝ (fun y => inducedMetric u y v w) x z
      = fderiv ℝ (fun y => ⟪fderiv ℝ u y v, fderiv ℝ u y w⟫) x z := rfl
    _ = ⟪fderiv ℝ u x v, fderiv ℝ (fun y => fderiv ℝ u y w) x z⟫
          + ⟪fderiv ℝ (fun y => fderiv ℝ u y v) x z, fderiv ℝ u x w⟫ :=
        fderiv_inner_apply ℝ hd1 hd2 z
    _ = ⟪fderiv ℝ u x v, fderiv ℝ (fderiv ℝ u) x z w⟫
          + ⟪fderiv ℝ (fderiv ℝ u) x z v, fderiv ℝ u x w⟫ := by
        rw [hclm w, hclm v]

/-- **Math.** Exercise 2.5.22 (coordinate-free core): the first-kind Christoffel
symbol of the induced metric equals the ambient inner product of the second
derivative of the parametrization with its differential,
`Γ_x(v, w, z) = ⟪D²u_x(v, w), Du_x z⟫`.  In coordinates this is
`Γ_{ij,k} = ∑_s u^s_{ij} u^s_k`. -/
theorem inducedChristoffelFirst_eq (hu : ContDiff ℝ ∞ u) (v w z : E) :
    inducedChristoffelFirst u x v w z
      = ⟪fderiv ℝ (fderiv ℝ u) x v w, fderiv ℝ u x z⟫ := by
  have hsymm : ∀ a b : E, fderiv ℝ (fderiv ℝ u) x a b = fderiv ℝ (fderiv ℝ u) x b a :=
    fun a b => (hu.contDiffAt.isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_cast)).eq a b
  rw [inducedChristoffelFirst, fderiv_inducedMetric hu w z,
    fderiv_inducedMetric hu v z, fderiv_inducedMetric hu v w]
  -- Cancel four inner products via second-derivative symmetry; the last swap uses
  -- the symmetry of the (real) inner product, and the surviving two combine.
  rw [hsymm w v, hsymm z w, hsymm z v]
  linarith [real_inner_comm (fderiv ℝ (fderiv ℝ u) x v z) (fderiv ℝ u x w)]

end InducedMetric

section Coordinates

variable {n N : ℕ}

/-- **Math.** Exercise 2.5.22, coordinate form.  For a smooth parametrization
`u : ℝ^n → ℝ^{n+m}` (here `ℝ^N`), the induced metric components and the
first-kind Christoffel symbols are, in the coordinate frame `∂_i`,
`g_{ij} = ∑_s u^s_i u^s_j` and `Γ_{ij,k} = ∑_s u^s_{ij} u^s_k`, where
`u^s_i = ∂u^s/∂x^i` and `u^s_{ij} = ∂²u^s/(∂x^i ∂x^j)`. -/
theorem exercise2_5_22
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (hu : ContDiff ℝ ∞ u) (x : EuclideanSpace ℝ (Fin n))
    (i j k : Fin n) :
    inducedMetric u x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
        = ∑ s, fderiv ℝ u x (EuclideanSpace.single i 1) s
            * fderiv ℝ u x (EuclideanSpace.single j 1) s ∧
    inducedChristoffelFirst u x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)
        = ∑ s, fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
            (EuclideanSpace.single j 1) s
            * fderiv ℝ u x (EuclideanSpace.single k 1) s := by
  refine ⟨?_, ?_⟩
  · rw [inducedMetric, PiLp.inner_apply]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  · rw [inducedChristoffelFirst_eq hu, PiLp.inner_apply]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _

end Coordinates

end PetersenLib
