import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.21 (transformation of Christoffel symbols)

Under a change of coordinates $x=x(\tilde x)$ the Christoffel symbols transform
inhomogeneously — the inhomogeneous (second-derivative) term is exactly what
makes them non-tensorial (\cref{rem:pet-ch2-christoffel-non-tensorial}).  The
first-kind form of Petersen's transformation law is
\[
  \tilde\Gamma_{ij,k}
  = \frac{\partial^2x^s}{\partial\tilde x^i\partial\tilde x^j}\frac{\partial x^\ell}{\partial\tilde x^k}g_{s\ell}
  + \frac{\partial x^s}{\partial\tilde x^i}\frac{\partial x^t}{\partial\tilde x^j}\frac{\partial x^\ell}{\partial\tilde x^k}\Gamma_{st,\ell}.
\]

The whole content is a statement about the transition map $\varphi:\tilde x\mapsto x$
and the ambient metric $g$ in the $x$-coordinates, so we formalize it directly:
`g` is a smooth field `B : F → (F →L[ℝ] F →L[ℝ] ℝ)` of (symmetric) bilinear
forms, `φ : E → F` is the smooth coordinate change, and the $\tilde x$-metric is
its pullback `B(φ x)(Dφ_x v, Dφ_x w)` (`coordPullbackMetric`).  Writing `Dφ_x` for the
differential and `D²φ_x` for the (symmetric) second derivative:

* `metricChristoffelFirst B y a b c` is the first-kind Christoffel symbol of the
  ambient metric, `½((D_a B)(b,c) + (D_b B)(a,c) − (D_c B)(a,b))`;
* `pullbackChristoffelFirst B φ x v w z` is the first-kind Christoffel symbol of
  the pullback metric;
* `exercise2_5_21` proves
  `pullbackChristoffelFirst B φ x v w z
     = B(φ x)(D²φ_x(v,w), Dφ_x z) + metricChristoffelFirst B (φ x)(Dφ_x v)(Dφ_x w)(Dφ_x z)`,
  i.e. exactly the first-kind law above (the first summand is the inhomogeneous
  $\partial^2x\cdot g$ term, the second the $\Gamma$ term contracted with $Dφ$).

The proof differentiates the pullback-metric components by the Leibniz and chain
rules (`fderiv_clm_apply`, `fderiv_comp`), then cancels the excess inner-product
terms using the symmetry of the ambient metric `B` and of the second derivative
`D²φ` (`IsSymmSndFDerivAt`).  Taking `B` constant $=\langle\cdot,\cdot\rangle$
recovers Exercise 2.5.22.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercise 21.
-/

open scoped ContDiff

namespace PetersenLib

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Math.** The pullback of an ambient metric `B` along a parametrization/change
of coordinates `φ`: `g̃_x(v,w) = B(φ x)(Dφ_x v, Dφ_x w)`. -/
noncomputable def coordPullbackMetric (B : F → (F →L[ℝ] F →L[ℝ] ℝ)) (φ : E → F)
    (x : E) (v w : E) : ℝ :=
  B (φ x) (fderiv ℝ φ x v) (fderiv ℝ φ x w)

/-- **Math.** The Christoffel symbol of the first kind of the ambient metric `B`
at `y`, `Γ(a,b,c) = ½((D_a B)(b,c) + (D_b B)(a,c) − (D_c B)(a,b))`, where `D_a`
is the directional derivative of the metric field. -/
noncomputable def metricChristoffelFirst (B : F → (F →L[ℝ] F →L[ℝ] ℝ))
    (y : F) (a b c : F) : ℝ :=
  (1 / 2 : ℝ) *
    (fderiv ℝ B y a b c + fderiv ℝ B y b a c - fderiv ℝ B y c a b)

/-- **Math.** The Christoffel symbol of the first kind of the pullback metric
`coordPullbackMetric B φ`, `Γ̃(v,w,z) = ½(D_v g̃(w,z) + D_w g̃(v,z) − D_z g̃(v,w))`. -/
noncomputable def pullbackChristoffelFirst (B : F → (F →L[ℝ] F →L[ℝ] ℝ))
    (φ : E → F) (x : E) (v w z : E) : ℝ :=
  (1 / 2 : ℝ) *
    (fderiv ℝ (fun y => coordPullbackMetric B φ y w z) x v
      + fderiv ℝ (fun y => coordPullbackMetric B φ y v z) x w
      - fderiv ℝ (fun y => coordPullbackMetric B φ y v w) x z)

variable {B : F → (F →L[ℝ] F →L[ℝ] ℝ)} {φ : E → F} {x : E}

/-- **Eng.** The directional derivative of a pullback-metric component, by the
Leibniz rule (`fderiv_clm_apply`) together with the chain rule for `y ↦ B(φ y)`
(`fderiv_comp`) and the derivative of `y ↦ Dφ_y v`:
`D_z g̃(v,w) = (D_{Dφ z}B)(Dφ v, Dφ w) + B(D²φ(z,v), Dφ w) + B(Dφ v, D²φ(z,w))`. -/
theorem fderiv_coordPullbackMetric (hB : ContDiff ℝ ∞ B) (hφ : ContDiff ℝ ∞ φ)
    (v w z : E) :
    fderiv ℝ (fun y => coordPullbackMetric B φ y v w) x z
      = (fderiv ℝ B (φ x) (fderiv ℝ φ x z)) (fderiv ℝ φ x v) (fderiv ℝ φ x w)
        + B (φ x) (fderiv ℝ (fderiv ℝ φ) x z v) (fderiv ℝ φ x w)
        + B (φ x) (fderiv ℝ φ x v) (fderiv ℝ (fderiv ℝ φ) x z w) := by
  show fderiv ℝ (fun y => B (φ y) (fderiv ℝ φ y v) (fderiv ℝ φ y w)) x z = _
  have hfd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((hφ.fderiv_right (m := 1) (by norm_cast)).differentiable one_ne_zero).differentiableAt
  have hp : DifferentiableAt ℝ (fun y => fderiv ℝ φ y v) x :=
    hfd.clm_apply (differentiableAt_const v)
  have hq : DifferentiableAt ℝ (fun y => fderiv ℝ φ y w) x :=
    hfd.clm_apply (differentiableAt_const w)
  have hBd : DifferentiableAt ℝ B (φ x) := (hB.differentiable (by norm_cast)).differentiableAt
  have hφd : DifferentiableAt ℝ φ x := (hφ.differentiable (by norm_cast)).differentiableAt
  have hBφ : DifferentiableAt ℝ (fun y => B (φ y)) x :=
    ((hB.differentiable (by norm_cast)).comp (hφ.differentiable (by norm_cast))).differentiableAt
  have hn : DifferentiableAt ℝ (fun y => B (φ y) (fderiv ℝ φ y v)) x := hBφ.clm_apply hp
  have hclmφ : ∀ a : E, fderiv ℝ (fun y => fderiv ℝ φ y a) x z
      = fderiv ℝ (fderiv ℝ φ) x z a := by
    intro a; rw [fderiv_clm_apply hfd (differentiableAt_const a)]; simp
  have hchain : fderiv ℝ (fun y => B (φ y)) x z = fderiv ℝ B (φ x) (fderiv ℝ φ x z) := by
    have h := fderiv_comp (𝕜 := ℝ) (g := B) (f := φ) (x := x) hBd hφd
    rw [show (fun y => B (φ y)) = B ∘ φ from rfl, h, ContinuousLinearMap.comp_apply]
  rw [fderiv_clm_apply hn hq, fderiv_clm_apply hBφ hp]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, hclmφ v, hclmφ w, hchain]
  ring

/-- **Math.** Exercise 2.5.21 (first-kind transformation law).  For a smooth
symmetric ambient metric `B` and a smooth coordinate change `φ`, the first-kind
Christoffel symbol of the pullback metric decomposes as the inhomogeneous
second-derivative term plus the ambient Christoffel symbol contracted with the
differential:
`Γ̃(v,w,z) = B(φ x)(D²φ(v,w), Dφ z) + Γ(Dφ v, Dφ w, Dφ z)`. -/
theorem exercise2_5_21 (hB : ContDiff ℝ ∞ B) (hφ : ContDiff ℝ ∞ φ)
    (hBsymm : ∀ y : F, ∀ a b : F, B y a b = B y b a) (v w z : E) :
    pullbackChristoffelFirst B φ x v w z
      = B (φ x) (fderiv ℝ (fderiv ℝ φ) x v w) (fderiv ℝ φ x z)
        + metricChristoffelFirst B (φ x)
            (fderiv ℝ φ x v) (fderiv ℝ φ x w) (fderiv ℝ φ x z) := by
  have hd2 : ∀ a b : E, fderiv ℝ (fderiv ℝ φ) x a b = fderiv ℝ (fderiv ℝ φ) x b a :=
    fun a b => (hφ.contDiffAt.isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_cast)).eq a b
  rw [pullbackChristoffelFirst, metricChristoffelFirst,
    fderiv_coordPullbackMetric hB hφ w z, fderiv_coordPullbackMetric hB hφ v z,
    fderiv_coordPullbackMetric hB hφ v w]
  -- Normalize the second-derivative arguments and use the symmetry of `B` so the
  -- excess `B(D²φ, Dφ)` terms cancel; the surviving one is `B(D²φ(v,w), Dφ z)`.
  rw [hd2 w v, hd2 z w, hd2 z v,
    hBsymm (φ x) (fderiv ℝ φ x w) (fderiv ℝ (fderiv ℝ φ) x v z)]
  ring

end PetersenLib
