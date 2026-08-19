import MorganTianLib.Ch02.TraceCommutation
import MorganTianLib.Ch03.RicciFlow.ScalarCurvatureSmooth
import Topping.RicciFlow.Evolution

/-!
# Covariant tensor fields with smooth components

Every formula of Topping's Chapter 2 that pulls a constant out of a covariant
derivative needs a regularity input: `∇_XA` is built from `X(A(Y))`, and a
directional derivative is only linear over constants where the function it
differentiates is differentiable. Iterating -- `∇²` differentiates `∇A` -- the
input has to be *smoothness*, not one degree of differentiability, since the
first derivative must be differentiable again.

This module isolates that input as `HasSmoothComponents A`: every evaluation
`A(Y₁,…,Y_k)` on smooth vector fields is a smooth function on `M`. Two facts
make it usable:

* it is preserved by `covDerivAlong`, hence by `∇²`. Note it is *not* claimed for
  the rough Laplacian: `traceFirstTwo` feeds `MorganTianLib.extendVector p` of a
  per-point orthonormal basis into the traced slots, and that extension is a
  `Classical.choose` whose dependence on `p` carries no regularity at all
  (`extendVector_apply` is its only property). Smoothness of `ΔA` would need the
  `orthoFrameField` route instead — the same smooth-frame gap that blocks the
  Bochner identity (inbox I-0494);
* the Ricci tensor field has it, because near any point `\Ric(X,Y)` is a finite
  sum of curvature pairings of the smooth orthonormal frame
  (`MorganTianLib.ricciField_eq_frame_sum` and `curvatureForm_contMDiff`).

With those, `∇²(cA) = c∇²A` becomes available for `c = -2` and `A = \Ric`, which
is exactly what substituting Ricci flow's `h = -2\Ric` into the first-variation
formulas requires.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Smooth components -/

/-- **Math.** A covariant tensor field has *smooth components* when its value on
every tuple of smooth vector fields is a smooth function on `M`. This is the
regularity hypothesis under which `∇` is linear over constants and can be
iterated. -/
def HasSmoothComponents {k : ℕ} (A : CovTensorField I M k) : Prop :=
  ∀ Y : Fin k → SmoothVectorField I M, ContMDiff I 𝓘(ℝ, ℝ) ∞ (A Y)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Smooth components give differentiable components, which is the
form the Leibniz computations consume. -/
theorem HasSmoothComponents.mdifferentiableAt {k : ℕ} {A : CovTensorField I M k}
    (hA : HasSmoothComponents A) (Y : Fin k → SmoothVectorField I M) (p : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (A Y) p :=
  ((hA Y).mdifferentiable (by norm_num)) p

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The covariant derivative of a tensor field with smooth components
again has smooth components: `∇_XA(Y) = X(A(Y)) - Σᵢ A(…,∇_XYᵢ,…)` is a
difference of a directional derivative of a smooth function and a finite sum of
evaluations of `A`. -/
theorem HasSmoothComponents.covDerivAlong {k : ℕ} {A : CovTensorField I M k}
    (hA : HasSmoothComponents A) (nabla : AffineConnection I M)
    (X : SmoothVectorField I M) :
    HasSmoothComponents (Topping.covDerivAlong nabla X A) := by
  intro Y
  have hfun : Topping.covDerivAlong nabla X A Y
      = fun p => X.dir (A Y) p
        - ∑ i, A (Function.update Y i (nabla.cov X (Y i))) p := rfl
  rw [hfun]
  exact (X.dir_contMDiff (hA Y)).sub
    (MorganTianLib.contMDiff_fun_sum fun i _ => hA _)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Hence `∇²_{X,Y}A` has smooth components whenever `A` does: it is a
difference of two iterated covariant derivatives. -/
theorem HasSmoothComponents.secondCovDerivAlong {k : ℕ}
    {A : CovTensorField I M k} (hA : HasSmoothComponents A)
    (nabla : AffineConnection I M) (X Y : SmoothVectorField I M) :
    HasSmoothComponents (Topping.secondCovDerivAlong nabla X Y A) := by
  intro Z
  have hfun : Topping.secondCovDerivAlong nabla X Y A Z
      = fun p => Topping.covDerivAlong nabla X
            (Topping.covDerivAlong nabla Y A) Z p
          - Topping.covDerivAlong nabla (nabla.cov X Y) A Z p := rfl
  rw [hfun]
  exact (((hA.covDerivAlong nabla Y).covDerivAlong nabla X) Z).sub
    ((hA.covDerivAlong nabla (nabla.cov X Y)) Z)

/-! ### Pulling constants out of covariant derivatives -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** `∇_X(cA) = c∇_XA` for a real constant `c`. Both terms of the
Leibniz formula are homogeneous: the directional derivative by
`SmoothVectorField.dir_const_mul`, which needs differentiability of `A(Y)`, and
the correction sum by distributivity. -/
theorem covDerivAlong_const_mul (nabla : AffineConnection I M)
    (X : SmoothVectorField I M) (c : ℝ) {k : ℕ} {A : CovTensorField I M k}
    (hA : ∀ (Y : Fin k → SmoothVectorField I M) (q : M),
      MDifferentiableAt I 𝓘(ℝ, ℝ) (A Y) q) :
    Topping.covDerivAlong nabla X
        (fun (Y : Fin k → SmoothVectorField I M) p => c * A Y p)
      = fun Y p => c * Topping.covDerivAlong nabla X A Y p := by
  funext Y p
  simp only [Topping.covDerivAlong]
  rw [X.dir_const_mul c p (hA Y p), ← Finset.mul_sum, mul_sub]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** `∇²_{X,Y}(cA) = c∇²_{X,Y}A`. This is the identity that makes the
Ricci-flow substitution `h = -2\Ric` legitimate inside the second-derivative
terms of the first-variation formulas: it is two applications of the
first-order homogeneity, and the inner one is applied to `∇A`, which is why
smoothness of `A` -- not mere differentiability -- is the hypothesis. -/
theorem secondCovDerivAlong_const_mul (nabla : AffineConnection I M)
    (X Y : SmoothVectorField I M) (c : ℝ) {k : ℕ} {A : CovTensorField I M k}
    (hA : HasSmoothComponents A) :
    Topping.secondCovDerivAlong nabla X Y
        (fun (Z : Fin k → SmoothVectorField I M) p => c * A Z p)
      = fun Z p => c * Topping.secondCovDerivAlong nabla X Y A Z p := by
  have hinner := covDerivAlong_const_mul nabla Y c hA.mdifferentiableAt
  have houter := covDerivAlong_const_mul nabla X c
    (hA.covDerivAlong nabla Y).mdifferentiableAt
  have hcross := covDerivAlong_const_mul nabla (nabla.cov X Y) c
    hA.mdifferentiableAt
  funext Z p
  simp only [Topping.secondCovDerivAlong]
  rw [hinner, houter, hcross, mul_sub]

/-! ### The Ricci tensor field has smooth components -/

/-- **Math.** The Ricci tensor of two smooth vector fields is a **smooth**
function on `M`. Near any point it agrees with its orthonormal-frame expansion,
a finite sum of curvature pairings of smooth fields, so smoothness of the
Gram--Schmidt frame gives smoothness of `\Ric(X,Y)`. This upgrades
`MorganTianLib.ricciField_mdifferentiableAt` from one derivative to all of
them, which is what iterating `∇` needs. -/
theorem ricciField_contMDiff (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g)
    (X W : SmoothVectorField I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (MorganTianLib.ricciField g nabla hLC X W) := by
  intro p
  have hs : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun q => ∑ j, nabla.curvatureForm g X
        (MorganTianLib.orthoFrameField g p j) W
        (MorganTianLib.orthoFrameField g p j) q) p :=
    ContMDiffAt.sum fun j _ =>
      (MorganTianLib.curvatureForm_contMDiff g nabla X
        (MorganTianLib.orthoFrameField g p j) W
        (MorganTianLib.orthoFrameField g p j)).contMDiffAt
  refine (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [(MorganTianLib.isOpen_orthoFrameSet (I := I) (M := M) p).mem_nhds
      (MorganTianLib.mem_orthoFrameSet_self (I := I) p)] with q hq
  exact MorganTianLib.ricciField_eq_frame_sum g nabla hLC p hq X W

/-- **Math.** Topping's Ricci tensor field, as a covariant `2`-tensor field, has
smooth components. -/
theorem hasSmoothComponents_ricciTensorField (g : RiemannianMetric I M) :
    HasSmoothComponents (ricciTensorField g) := by
  intro Y
  have hfun : ricciTensorField g Y
      = MorganTianLib.ricciField g g.leviCivitaConnection
          (isLeviCivita_leviCivitaConnection g) (Y 0) (Y 1) := by
    funext r
    rw [ricciTensorField, MorganTianLib.ricciField, ← ricciTensorAt_eq_ricciAt]
  rw [hfun]
  exact ricciField_contMDiff g g.leviCivitaConnection
    (isLeviCivita_leviCivitaConnection g) (Y 0) (Y 1)

end Topping

end
