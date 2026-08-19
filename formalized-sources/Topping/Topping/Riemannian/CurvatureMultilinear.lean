import Topping.Riemannian.FrameTrace
import Topping.Riemannian.SmoothTensor
import Topping.RicciFlow.Evolution
import MorganTianLib.Ch01.SecondBianchi
import MorganTianLib.Ch03.RicciFlow.ScalarCurvatureSmooth

/-!
# The curvature tensors are pointwise multilinear

`FrameTrace` proves that `tr₁₂` and `|·|²` are frame-independent *for pointwise
multilinear tensors*. That hypothesis is genuine — `CovTensorField I M k` is an
arbitrary map on tuples of vector fields — so the frame results are worth nothing
until something satisfies it. This module supplies the witnesses that matter:

* `isPointwiseMultilinear_riemannTensorField` — `\Rm` as a covariant `4`-tensor
  field;
* `isPointwiseMultilinear_ricciTensorField` — `\Ric` as a covariant `2`-tensor;
* `isPointwiseMultilinear_metricTensorField` — `g` itself.

For `\Rm` the content is `IsAlgCurvatureForm`: `riemannCurvatureAt g p` is
additive and homogeneous in each of its four arguments (`add_left`/`add_two`/…,
`smul_left`/`smul_two`/… of DoCarmo's algebraic curvature form), and it depends
only on the arguments' values at `p` by construction. For `\Ric` it is
`ricciTensorAt`'s being a genuine `→ₗ[ℝ] →ₗ[ℝ] ℝ`, and for `g` it is bilinearity
of `metricInner`.

Consequently `|\Rm|²` and `|\Ric|²` are computed by *any* orthonormal frame and,
via `exists_smooth_frame_normSqAt`, by a smooth local one — the statement the
curvature Bochner identity was blocked on.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### A slot-wise criterion

For a tensor field defined by reading off the arguments' values at `p` and
feeding them to a pointwise function, `IsPointwiseTensorial` is immediate and
multilinearity reduces to slot-wise linearity of that function. The two `Fin`
case splits are packaged once here. -/

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** A tensor field of the form `Y p ↦ f p (Y 0 p) … (Y (k-1) p)` — one
that reads only the values at `p` — is pointwise multilinear as soon as the
underlying pointwise function `b` is linear in each slot. -/
theorem isPointwiseMultilinear_of_pointwise {k : ℕ}
    {A : CovTensorField I M k} {p : M}
    (b : (Fin k → TangentSpace I p) → ℝ)
    (hval : ∀ Y : Fin k → SmoothVectorField I M, A Y p = b (fun i => Y i p))
    (hadd : ∀ (i : Fin k) (v : Fin k → TangentSpace I p) (x y : TangentSpace I p),
      b (Function.update v i (x + y))
        = b (Function.update v i x) + b (Function.update v i y))
    (hsmul : ∀ (i : Fin k) (v : Fin k → TangentSpace I p) (c : ℝ)
      (x : TangentSpace I p),
      b (Function.update v i (c • x)) = c * b (Function.update v i x)) :
    IsPointwiseMultilinear A p := by
  have hpv : ∀ v : Fin k → TangentSpace I p, pointwiseValue A p v = b v := by
    intro v
    rw [pointwiseValue, hval]
    simp
  refine ⟨fun Y Z hYZ => ?_, ?_, ?_⟩
  · rw [hval, hval]
    exact congrArg b (funext hYZ)
  · intro i v x y; rw [hpv, hpv, hpv]; exact hadd i v x y
  · intro i v c x; rw [hpv, hpv]; exact hsmul i v c x

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** A genuine covariant `4`-tensor in the vector-field sense gives a
pointwise multilinear `CovTensorField`.  The only work is passing from chosen
extensions of tangent vectors to arbitrary vector fields; that is precisely
`covariantTensor4_congr_apply`. -/
theorem isPointwiseMultilinear_of_isCovariantTensor4
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ))
    (hT : IsCovariantTensor4 T) (A : CovTensorField I M 4)
    (hA : ∀ (Y : Fin 4 → SmoothVectorField I M) (q : M),
      A Y q = T (Y 0) (Y 1) (Y 2) (Y 3) q) (p : M) :
    IsPointwiseMultilinear A p := by
  classical
  refine isPointwiseMultilinear_of_pointwise
    (fun v => T (MorganTianLib.extendVector p (v 0))
      (MorganTianLib.extendVector p (v 1))
      (MorganTianLib.extendVector p (v 2))
      (MorganTianLib.extendVector p (v 3)) p) ?_ ?_ ?_
  · intro Y
    rw [hA]
    exact MorganTianLib.covariantTensor4_congr_apply T hT
      (MorganTianLib.extendVector_apply p (Y 0 p)).symm
      (MorganTianLib.extendVector_apply p (Y 1 p)).symm
      (MorganTianLib.extendVector_apply p (Y 2 p)).symm
      (MorganTianLib.extendVector_apply p (Y 3 p)).symm
  · intro i v x y
    fin_cases i <;> simp
    · have h : T (MorganTianLib.extendVector p (x + y))
          (MorganTianLib.extendVector p (v 1)) (MorganTianLib.extendVector p (v 2))
          (MorganTianLib.extendVector p (v 3)) p =
          T (MorganTianLib.extendVector p x + MorganTianLib.extendVector p y)
            (MorganTianLib.extendVector p (v 1)) (MorganTianLib.extendVector p (v 2))
            (MorganTianLib.extendVector p (v 3)) p :=
        MorganTianLib.covariantTensor4_congr_apply T hT (by simp) rfl rfl rfl
      rw [h, hT.add₁]
    · have h : T (MorganTianLib.extendVector p (v 0))
          (MorganTianLib.extendVector p (x + y)) (MorganTianLib.extendVector p (v 2))
          (MorganTianLib.extendVector p (v 3)) p =
          T (MorganTianLib.extendVector p (v 0))
            (MorganTianLib.extendVector p x + MorganTianLib.extendVector p y)
            (MorganTianLib.extendVector p (v 2)) (MorganTianLib.extendVector p (v 3)) p :=
        MorganTianLib.covariantTensor4_congr_apply T hT rfl (by simp) rfl rfl
      rw [h, hT.add₂]
    · have h : T (MorganTianLib.extendVector p (v 0))
          (MorganTianLib.extendVector p (v 1)) (MorganTianLib.extendVector p (x + y))
          (MorganTianLib.extendVector p (v 3)) p =
          T (MorganTianLib.extendVector p (v 0)) (MorganTianLib.extendVector p (v 1))
            (MorganTianLib.extendVector p x + MorganTianLib.extendVector p y)
            (MorganTianLib.extendVector p (v 3)) p :=
        MorganTianLib.covariantTensor4_congr_apply T hT rfl rfl (by simp) rfl
      rw [h, hT.add₃]
    · have h : T (MorganTianLib.extendVector p (v 0))
          (MorganTianLib.extendVector p (v 1)) (MorganTianLib.extendVector p (v 2))
          (MorganTianLib.extendVector p (x + y)) p =
          T (MorganTianLib.extendVector p (v 0)) (MorganTianLib.extendVector p (v 1))
            (MorganTianLib.extendVector p (v 2))
            (MorganTianLib.extendVector p x + MorganTianLib.extendVector p y) p :=
        MorganTianLib.covariantTensor4_congr_apply T hT rfl rfl rfl (by simp)
      rw [h, hT.add₄]
  · intro i v c x
    have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
    fin_cases i <;> simp
    · have h : T (MorganTianLib.extendVector p (c • x))
          (MorganTianLib.extendVector p (v 1)) (MorganTianLib.extendVector p (v 2))
          (MorganTianLib.extendVector p (v 3)) p =
          T (SmoothVectorField.smul (fun _ => c) hc (MorganTianLib.extendVector p x))
            (MorganTianLib.extendVector p (v 1)) (MorganTianLib.extendVector p (v 2))
            (MorganTianLib.extendVector p (v 3)) p :=
        MorganTianLib.covariantTensor4_congr_apply T hT (by simp) rfl rfl rfl
      rw [h, hT.smul₁ (fun _ => c) hc]
    · have h : T (MorganTianLib.extendVector p (v 0))
          (MorganTianLib.extendVector p (c • x)) (MorganTianLib.extendVector p (v 2))
          (MorganTianLib.extendVector p (v 3)) p =
          T (MorganTianLib.extendVector p (v 0))
            (SmoothVectorField.smul (fun _ => c) hc (MorganTianLib.extendVector p x))
            (MorganTianLib.extendVector p (v 2)) (MorganTianLib.extendVector p (v 3)) p :=
        MorganTianLib.covariantTensor4_congr_apply T hT rfl (by simp) rfl rfl
      rw [h, hT.smul₂ (fun _ => c) hc]
    · have h : T (MorganTianLib.extendVector p (v 0))
          (MorganTianLib.extendVector p (v 1)) (MorganTianLib.extendVector p (c • x))
          (MorganTianLib.extendVector p (v 3)) p =
          T (MorganTianLib.extendVector p (v 0)) (MorganTianLib.extendVector p (v 1))
            (SmoothVectorField.smul (fun _ => c) hc (MorganTianLib.extendVector p x))
            (MorganTianLib.extendVector p (v 3)) p :=
        MorganTianLib.covariantTensor4_congr_apply T hT rfl rfl (by simp) rfl
      rw [h, hT.smul₃ (fun _ => c) hc]
    · have h : T (MorganTianLib.extendVector p (v 0))
          (MorganTianLib.extendVector p (v 1)) (MorganTianLib.extendVector p (v 2))
          (MorganTianLib.extendVector p (c • x)) p =
          T (MorganTianLib.extendVector p (v 0)) (MorganTianLib.extendVector p (v 1))
            (MorganTianLib.extendVector p (v 2))
            (SmoothVectorField.smul (fun _ => c) hc (MorganTianLib.extendVector p x)) p :=
        MorganTianLib.covariantTensor4_congr_apply T hT rfl rfl rfl (by simp)
      rw [h, hT.smul₄ (fun _ => c) hc]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** A covariant `2`-tensor is pointwise local in both slots. -/
theorem covariantTensor2_congr_apply
    (T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (hT : IsCovariantTensor2 T)
    {X X' Y Y' : SmoothVectorField I M} {p : M}
    (hX : X p = X' p) (hY : Y p = Y' p) :
    T X Y p = T X' Y' p := by
  have h1 : T X Y p = T X' Y p :=
    MorganTianLib.tensorial_congr_apply (fun A => T A Y)
      (fun A B q => hT.add_left A B Y q)
      (fun f hf A q => hT.smul_left f hf A Y q) hX
  have h2 : T X' Y p = T X' Y' p :=
    MorganTianLib.tensorial_congr_apply (fun B => T X' B)
      (fun A B q => hT.add_right X' A B q)
      (fun f hf A q => hT.smul_right f hf X' A q) hY
  rw [h1, h2]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** A genuine covariant `2`-tensor gives a pointwise multilinear
`CovTensorField` when its tuple representation is supplied. -/
theorem isPointwiseMultilinear_of_isCovariantTensor2
    (T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (hT : IsCovariantTensor2 T) (A : CovTensorField I M 2)
    (hA : ∀ (Y : Fin 2 → SmoothVectorField I M) (q : M),
      A Y q = T (Y 0) (Y 1) q) (p : M) :
    IsPointwiseMultilinear A p := by
  classical
  refine isPointwiseMultilinear_of_pointwise
    (fun v => T (MorganTianLib.extendVector p (v 0))
      (MorganTianLib.extendVector p (v 1)) p) ?_ ?_ ?_
  · intro Y
    rw [hA]
    exact covariantTensor2_congr_apply T hT
      (MorganTianLib.extendVector_apply p (Y 0 p)).symm
      (MorganTianLib.extendVector_apply p (Y 1 p)).symm
  · intro i v x y
    fin_cases i <;> simp
    · have h :
          T (MorganTianLib.extendVector p (x + y))
              (MorganTianLib.extendVector p (v 1)) p =
            T (MorganTianLib.extendVector p x + MorganTianLib.extendVector p y)
              (MorganTianLib.extendVector p (v 1)) p :=
        covariantTensor2_congr_apply T hT (by simp) rfl
      rw [h, hT.add_left]
    · have h :
          T (MorganTianLib.extendVector p (v 0))
              (MorganTianLib.extendVector p (x + y)) p =
            T (MorganTianLib.extendVector p (v 0))
              (MorganTianLib.extendVector p x + MorganTianLib.extendVector p y) p :=
        covariantTensor2_congr_apply T hT rfl (by simp)
      rw [h, hT.add_right]
  · intro i v c x
    have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
    fin_cases i <;> simp
    · have h :
          T (MorganTianLib.extendVector p (c • x))
              (MorganTianLib.extendVector p (v 1)) p =
            T (SmoothVectorField.smul (fun _ => c) hc
                (MorganTianLib.extendVector p x))
              (MorganTianLib.extendVector p (v 1)) p :=
        covariantTensor2_congr_apply T hT (by simp) rfl
      rw [h, hT.smul_left (fun _ => c) hc]
    · have h :
          T (MorganTianLib.extendVector p (v 0))
              (MorganTianLib.extendVector p (c • x)) p =
            T (MorganTianLib.extendVector p (v 0))
              (SmoothVectorField.smul (fun _ => c) hc
                (MorganTianLib.extendVector p x)) p :=
        covariantTensor2_congr_apply T hT rfl (by simp)
      rw [h, hT.smul_right (fun _ => c) hc]

/-! ### Covariant derivatives of order-four tensors -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The covariant differential of a smooth covariant `4`-tensor is
again covariant in its four tensor slots.  In a slot multiplied by a smooth
function, the two `U(f)` terms from the scalar Leibniz rule and the connection
Leibniz rule cancel. -/
theorem isCovariantTensor4_covariantDifferential4
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ))
    (hT : IsCovariantTensor4 T)
    (hsm : ∀ X Y Z W, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y Z W))
    (U : SmoothVectorField I M) :
    IsCovariantTensor4
      (fun X Y Z W => MorganTianLib.covariantDifferential4 nabla T X Y Z W U) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X₁ X₂ Y Z W p
    have hfun : T (X₁ + X₂) Y Z W =
        fun q => T X₁ Y Z W q + T X₂ Y Z W q := by
      funext q
      exact hT.add₁ X₁ X₂ Y Z W q
    simp only [MorganTianLib.covariantDifferential4]
    rw [hfun, U.dir_add p ((hsm X₁ Y Z W).mdifferentiableAt (by simp))
      ((hsm X₂ Y Z W).mdifferentiableAt (by simp)), nabla.add_right U X₁ X₂]
    simp only [hT.add₁]
    ring
  · intro X Y₁ Y₂ Z W p
    have hfun : T X (Y₁ + Y₂) Z W =
        fun q => T X Y₁ Z W q + T X Y₂ Z W q := by
      funext q
      exact hT.add₂ X Y₁ Y₂ Z W q
    simp only [MorganTianLib.covariantDifferential4]
    rw [hfun, U.dir_add p ((hsm X Y₁ Z W).mdifferentiableAt (by simp))
      ((hsm X Y₂ Z W).mdifferentiableAt (by simp)), nabla.add_right U Y₁ Y₂]
    simp only [hT.add₂]
    ring
  · intro X Y Z₁ Z₂ W p
    have hfun : T X Y (Z₁ + Z₂) W =
        fun q => T X Y Z₁ W q + T X Y Z₂ W q := by
      funext q
      exact hT.add₃ X Y Z₁ Z₂ W q
    simp only [MorganTianLib.covariantDifferential4]
    rw [hfun, U.dir_add p ((hsm X Y Z₁ W).mdifferentiableAt (by simp))
      ((hsm X Y Z₂ W).mdifferentiableAt (by simp)), nabla.add_right U Z₁ Z₂]
    simp only [hT.add₃]
    ring
  · intro X Y Z W₁ W₂ p
    have hfun : T X Y Z (W₁ + W₂) =
        fun q => T X Y Z W₁ q + T X Y Z W₂ q := by
      funext q
      exact hT.add₄ X Y Z W₁ W₂ q
    simp only [MorganTianLib.covariantDifferential4]
    rw [hfun, U.dir_add p ((hsm X Y Z W₁).mdifferentiableAt (by simp))
      ((hsm X Y Z W₂).mdifferentiableAt (by simp)), nabla.add_right U W₁ W₂]
    simp only [hT.add₄]
    ring
  · intro f hf X Y Z W p
    have hfun : T (SmoothVectorField.smul f hf X) Y Z W =
        fun q => f q * T X Y Z W q := by
      funext q
      exact hT.smul₁ f hf X Y Z W q
    simp only [MorganTianLib.covariantDifferential4]
    rw [hfun, U.dir_mul p (hf.mdifferentiableAt (by simp))
      ((hsm X Y Z W).mdifferentiableAt (by simp)), nabla.cov_smul_right hf U X]
    simp only [hT.add₁, hT.smul₁]
    ring
  · intro f hf X Y Z W p
    have hfun : T X (SmoothVectorField.smul f hf Y) Z W =
        fun q => f q * T X Y Z W q := by
      funext q
      exact hT.smul₂ f hf X Y Z W q
    simp only [MorganTianLib.covariantDifferential4]
    rw [hfun, U.dir_mul p (hf.mdifferentiableAt (by simp))
      ((hsm X Y Z W).mdifferentiableAt (by simp)), nabla.cov_smul_right hf U Y]
    simp only [hT.add₂, hT.smul₂]
    ring
  · intro f hf X Y Z W p
    have hfun : T X Y (SmoothVectorField.smul f hf Z) W =
        fun q => f q * T X Y Z W q := by
      funext q
      exact hT.smul₃ f hf X Y Z W q
    simp only [MorganTianLib.covariantDifferential4]
    rw [hfun, U.dir_mul p (hf.mdifferentiableAt (by simp))
      ((hsm X Y Z W).mdifferentiableAt (by simp)), nabla.cov_smul_right hf U Z]
    simp only [hT.add₃, hT.smul₃]
    ring
  · intro f hf X Y Z W p
    have hfun : T X Y Z (SmoothVectorField.smul f hf W) =
        fun q => f q * T X Y Z W q := by
      funext q
      exact hT.smul₄ f hf X Y Z W q
    simp only [MorganTianLib.covariantDifferential4]
    rw [hfun, U.dir_mul p (hf.mdifferentiableAt (by simp))
      ((hsm X Y Z W).mdifferentiableAt (by simp)), nabla.cov_smul_right hf U W]
    simp only [hT.add₄, hT.smul₄]
    ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The covariant differential of a tensor with smooth components
again has smooth components. -/
theorem covariantDifferential4_contMDiff
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ))
    (hsm : ∀ X Y Z W, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y Z W))
    (X Y Z W U : SmoothVectorField I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (MorganTianLib.covariantDifferential4 nabla T X Y Z W U) := by
  exact (((U.dir_contMDiff (hsm X Y Z W)).sub
    (hsm (nabla.cov U X) Y Z W)).sub
    (hsm X (nabla.cov U Y) Z W)).sub
    (hsm X Y (nabla.cov U Z) W) |>.sub
    (hsm X Y Z (nabla.cov U W))

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Topping's tuple-based `covDerivAlong` agrees with the standard
four-slot covariant differential whenever the tuple field represents `T`. -/
theorem covDerivAlong_eq_covariantDifferential4
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ))
    (A : CovTensorField I M 4)
    (hA : ∀ (Y : Fin 4 → SmoothVectorField I M) (q : M),
      A Y q = T (Y 0) (Y 1) (Y 2) (Y 3) q)
    (U : SmoothVectorField I M) (Y : Fin 4 → SmoothVectorField I M) (p : M) :
    covDerivAlong nabla U A Y p =
      MorganTianLib.covariantDifferential4 nabla T (Y 0) (Y 1) (Y 2) (Y 3) U p := by
  have hfun : A Y = fun q => T (Y 0) (Y 1) (Y 2) (Y 3) q := by
    funext q
    exact hA Y q
  rw [covDerivAlong_apply, hfun, Fin.sum_univ_four]
  simp [hA, MorganTianLib.covariantDifferential4, Function.update]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Topping's second covariant derivative agrees with the iterated
four-slot covariant differential, including the `∇_{∇_U V}` correction. -/
theorem secondCovDerivAlong_eq_iteratedCovariantDifferential4
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ))
    (A : CovTensorField I M 4)
    (hA : ∀ (Y : Fin 4 → SmoothVectorField I M) (q : M),
      A Y q = T (Y 0) (Y 1) (Y 2) (Y 3) q)
    (U V : SmoothVectorField I M)
    (Y : Fin 4 → SmoothVectorField I M) (p : M) :
    secondCovDerivAlong nabla U V A Y p =
      MorganTianLib.covariantDifferential4 nabla
          (fun X Y Z W =>
            MorganTianLib.covariantDifferential4 nabla T X Y Z W V)
          (Y 0) (Y 1) (Y 2) (Y 3) U p
        - MorganTianLib.covariantDifferential4 nabla T
            (Y 0) (Y 1) (Y 2) (Y 3) (nabla.cov U V) p := by
  have hV :
      ∀ (Z : Fin 4 → SmoothVectorField I M) (q : M),
        covDerivAlong nabla V A Z q =
          MorganTianLib.covariantDifferential4 nabla T
            (Z 0) (Z 1) (Z 2) (Z 3) V q :=
    fun Z q => covDerivAlong_eq_covariantDifferential4 nabla T A hA V Z q
  rw [secondCovDerivAlong,
    covDerivAlong_eq_covariantDifferential4 nabla
      (fun X Y Z W =>
        MorganTianLib.covariantDifferential4 nabla T X Y Z W V)
      (covDerivAlong nabla V A) hV U Y p,
    covDerivAlong_eq_covariantDifferential4 nabla T A hA
      (nabla.cov U V) Y p]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The covariant differential of a smooth covariant `2`-tensor is
again covariant in its two tensor slots. -/
theorem isCovariantTensor2_covariantDifferential2
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (hT : IsCovariantTensor2 T)
    (hsm : ∀ X Y, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y))
    (U : SmoothVectorField I M) :
    IsCovariantTensor2
      (fun X Y => nabla.covariantDifferential2 T X Y U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X₁ X₂ Y p
    have hfun : T (X₁ + X₂) Y =
        fun q => T X₁ Y q + T X₂ Y q := by
      funext q
      exact hT.add_left X₁ X₂ Y q
    simp only [AffineConnection.covariantDifferential2]
    rw [hfun, U.dir_add p ((hsm X₁ Y).mdifferentiableAt (by simp))
      ((hsm X₂ Y).mdifferentiableAt (by simp)), nabla.add_right U X₁ X₂]
    simp only [hT.add_left]
    ring
  · intro X Y₁ Y₂ p
    have hfun : T X (Y₁ + Y₂) =
        fun q => T X Y₁ q + T X Y₂ q := by
      funext q
      exact hT.add_right X Y₁ Y₂ q
    simp only [AffineConnection.covariantDifferential2]
    rw [hfun, U.dir_add p ((hsm X Y₁).mdifferentiableAt (by simp))
      ((hsm X Y₂).mdifferentiableAt (by simp)), nabla.add_right U Y₁ Y₂]
    simp only [hT.add_right]
    ring
  · intro f hf X Y p
    have hfun : T (SmoothVectorField.smul f hf X) Y =
        fun q => f q * T X Y q := by
      funext q
      exact hT.smul_left f hf X Y q
    simp only [AffineConnection.covariantDifferential2]
    rw [hfun, U.dir_mul p (hf.mdifferentiableAt (by simp))
      ((hsm X Y).mdifferentiableAt (by simp)), nabla.cov_smul_right hf U X]
    simp only [hT.add_left, hT.smul_left]
    ring
  · intro f hf X Y p
    have hfun : T X (SmoothVectorField.smul f hf Y) =
        fun q => f q * T X Y q := by
      funext q
      exact hT.smul_right f hf X Y q
    simp only [AffineConnection.covariantDifferential2]
    rw [hfun, U.dir_mul p (hf.mdifferentiableAt (by simp))
      ((hsm X Y).mdifferentiableAt (by simp)), nabla.cov_smul_right hf U Y]
    simp only [hT.add_right, hT.smul_right]
    ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Topping's tuple-based `covDerivAlong` agrees with the standard
two-slot covariant differential whenever the tuple field represents `T`. -/
theorem covDerivAlong_eq_covariantDifferential2
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (A : CovTensorField I M 2)
    (hA : ∀ (Y : Fin 2 → SmoothVectorField I M) (q : M),
      A Y q = T (Y 0) (Y 1) q)
    (U : SmoothVectorField I M) (Y : Fin 2 → SmoothVectorField I M) (p : M) :
    covDerivAlong nabla U A Y p =
      nabla.covariantDifferential2 T (Y 0) (Y 1) U p := by
  have hfun : A Y = fun q => T (Y 0) (Y 1) q := by
    funext q
    exact hA Y q
  rw [covDerivAlong_apply, hfun, Fin.sum_univ_two]
  simp [hA, AffineConnection.covariantDifferential2, Function.update]
  ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** A covariant `2`-tensor representation gives pointwise
multilinearity of its tuple-based covariant derivative. -/
theorem isPointwiseMultilinear_covDerivAlong_two
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (hT : IsCovariantTensor2 T)
    (hsm : ∀ X Y, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y))
    (A : CovTensorField I M 2)
    (hA : ∀ (Y : Fin 2 → SmoothVectorField I M) (q : M),
      A Y q = T (Y 0) (Y 1) q)
    (U : SmoothVectorField I M) (p : M) :
    IsPointwiseMultilinear (covDerivAlong nabla U A) p := by
  have hCD := isCovariantTensor2_covariantDifferential2 nabla T hT hsm U
  refine isPointwiseMultilinear_of_isCovariantTensor2
    (fun X Y => nabla.covariantDifferential2 T X Y U) hCD
    (covDerivAlong nabla U A) ?_ p
  intro Y q
  exact covDerivAlong_eq_covariantDifferential2 nabla T A hA U Y q

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Topping's corrected second covariant derivative agrees with the
iterated two-slot covariant differential. -/
theorem secondCovDerivAlong_eq_iteratedCovariantDifferential2
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (A : CovTensorField I M 2)
    (hA : ∀ (Y : Fin 2 → SmoothVectorField I M) (q : M),
      A Y q = T (Y 0) (Y 1) q)
    (U V : SmoothVectorField I M)
    (Y : Fin 2 → SmoothVectorField I M) (p : M) :
    secondCovDerivAlong nabla U V A Y p =
      nabla.covariantDifferential2
          (fun X Y => nabla.covariantDifferential2 T X Y V)
          (Y 0) (Y 1) U p
        - nabla.covariantDifferential2 T (Y 0) (Y 1) (nabla.cov U V) p := by
  have hV :
      ∀ (Z : Fin 2 → SmoothVectorField I M) (q : M),
        covDerivAlong nabla V A Z q =
          nabla.covariantDifferential2 T (Z 0) (Z 1) V q :=
    fun Z q => covDerivAlong_eq_covariantDifferential2 nabla T A hA V Z q
  rw [secondCovDerivAlong,
    covDerivAlong_eq_covariantDifferential2 nabla
      (fun X Y => nabla.covariantDifferential2 T X Y V)
      (covDerivAlong nabla V A) hV U Y p,
    covDerivAlong_eq_covariantDifferential2 nabla T A hA
      (nabla.cov U V) Y p]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** For a torsion-free connection, the commutator of the corrected
second covariant derivatives of a smooth covariant `2`-tensor is the sum of the
curvature actions in its two slots. -/
theorem correctedIteratedCovariantDifferential2_sub_swap
    (nabla : AffineConnection I M) (hsym : nabla.IsSymmetric)
    (T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (hT : IsCovariantTensor2 T)
    (hsm : ∀ X Y, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y))
    (X Y U V : SmoothVectorField I M) (p : M) :
    (nabla.covariantDifferential2
          (fun A B => nabla.covariantDifferential2 T A B V) X Y U p
        - nabla.covariantDifferential2 T X Y (nabla.cov U V) p)
      - (nabla.covariantDifferential2
          (fun A B => nabla.covariantDifferential2 T A B U) X Y V p
        - nabla.covariantDifferential2 T X Y (nabla.cov V U) p) =
      T (nabla.curvature U V X) Y p + T X (nabla.curvature U V Y) p := by
  have dir_sub_smooth (Q : SmoothVectorField I M) {f h : M → ℝ} (q : M)
      (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) :
      Q.dir (fun r => f r - h r) q = Q.dir f q - Q.dir h q := by
    simp only [SmoothVectorField.dir]
    rw [show (fun r => f r - h r) = f - h from rfl,
      mfderiv_sub (hf.mdifferentiableAt (by simp))
        (hh.mdifferentiableAt (by simp))]
    rfl
  have hdirCov (Q A B R : SmoothVectorField I M) :
      Q.dir (nabla.covariantDifferential2 T A B R) p =
        Q.dir (R.dir (T A B)) p
          - Q.dir (T (nabla.cov R A) B) p
          - Q.dir (T A (nabla.cov R B)) p := by
    have h0 := R.dir_contMDiff (hsm A B)
    have h1 := hsm (nabla.cov R A) B
    have h2 := hsm A (nabla.cov R B)
    change Q.dir (fun q => R.dir (T A B) q
      - T (nabla.cov R A) B q - T A (nabla.cov R B) q) p = _
    rw [dir_sub_smooth Q p (h0.sub h1) h2,
      dir_sub_smooth Q p h0 h1]
  have hbase :
      U.dir (V.dir (T X Y)) p - (nabla.cov U V).dir (T X Y) p =
        V.dir (U.dir (T X Y)) p - (nabla.cov V U).dir (T X Y) p := by
    simpa only [MorganTianLib.hessian] using
      (MorganTianLib.hessian_symm nabla hsym (hsm X Y) U V p)
  have hbr : bracketField U V = nabla.cov U V - nabla.cov V U := by
    ext q
    rw [SmoothVectorField.sub_apply, bracketField_apply]
    exact (hsym U V q).symm
  have hcurv (A : SmoothVectorField I M) :
      nabla.curvature U V A =
        (nabla.cov V (nabla.cov U A) - nabla.cov U (nabla.cov V A))
          + (nabla.cov (nabla.cov U V) A - nabla.cov (nabla.cov V U) A) := by
    ext q
    simp only [nabla.curvature_apply, hbr, nabla.cov_sub_left,
      SmoothVectorField.add_apply, SmoothVectorField.sub_apply]
  have hslot (S : SmoothVectorField I M → M → ℝ)
      (hadd : ∀ A B q, S (A + B) q = S A q + S B q)
      (A : SmoothVectorField I M) :
      (S (nabla.cov V (nabla.cov U A)) p
          - S (nabla.cov U (nabla.cov V A)) p)
        + (S (nabla.cov (nabla.cov U V) A) p
          - S (nabla.cov (nabla.cov V U) A) p)
        = S (nabla.curvature U V A) p := by
    symm
    calc
      S (nabla.curvature U V A) p =
          S ((nabla.cov V (nabla.cov U A) - nabla.cov U (nabla.cov V A))
            + (nabla.cov (nabla.cov U V) A - nabla.cov (nabla.cov V U) A)) p := by
              rw [hcurv A]
      _ = S (nabla.cov V (nabla.cov U A) - nabla.cov U (nabla.cov V A)) p
          + S (nabla.cov (nabla.cov U V) A - nabla.cov (nabla.cov V U) A) p :=
            hadd _ _ p
      _ = _ := by
        rw [MorganTianLib.tensorial_sub_apply S hadd
              (nabla.cov V (nabla.cov U A)) (nabla.cov U (nabla.cov V A)) p,
          MorganTianLib.tensorial_sub_apply S hadd
              (nabla.cov (nabla.cov U V) A) (nabla.cov (nabla.cov V U) A) p]
  have hX := hslot (fun A => T A Y)
    (fun A B q => hT.add_left A B Y q) X
  have hY := hslot (fun A => T X A)
    (fun A B q => hT.add_right X A B q) Y
  change
    (U.dir (nabla.covariantDifferential2 T X Y V) p
      - nabla.covariantDifferential2 T (nabla.cov U X) Y V p
      - nabla.covariantDifferential2 T X (nabla.cov U Y) V p
      - nabla.covariantDifferential2 T X Y (nabla.cov U V) p)
    - (V.dir (nabla.covariantDifferential2 T X Y U) p
      - nabla.covariantDifferential2 T (nabla.cov V X) Y U p
      - nabla.covariantDifferential2 T X (nabla.cov V Y) U p
      - nabla.covariantDifferential2 T X Y (nabla.cov V U) p) = _
  rw [hdirCov U X Y V, hdirCov V X Y U]
  simp only [AffineConnection.covariantDifferential2]
  linear_combination hbase + hX + hY

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** For a torsion-free connection, the commutator of the two
corrected second covariant derivatives of a smooth covariant `4`-tensor is the
sum of the curvature action in its four slots.  The order and sign agree with
the do Carmo convention used by `AffineConnection.curvature`. -/
theorem correctedIteratedCovariantDifferential4_sub_swap
    (nabla : AffineConnection I M) (hsym : nabla.IsSymmetric)
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ))
    (hT : IsCovariantTensor4 T)
    (hsm : ∀ X Y Z W, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y Z W))
    (X Y Z W U V : SmoothVectorField I M) (p : M) :
    (MorganTianLib.covariantDifferential4 nabla
          (fun A B C D =>
            MorganTianLib.covariantDifferential4 nabla T A B C D V)
          X Y Z W U p
        - MorganTianLib.covariantDifferential4 nabla T X Y Z W
            (nabla.cov U V) p)
      - (MorganTianLib.covariantDifferential4 nabla
          (fun A B C D =>
            MorganTianLib.covariantDifferential4 nabla T A B C D U)
          X Y Z W V p
        - MorganTianLib.covariantDifferential4 nabla T X Y Z W
            (nabla.cov V U) p) =
      T (nabla.curvature U V X) Y Z W p
        + T X (nabla.curvature U V Y) Z W p
        + T X Y (nabla.curvature U V Z) W p
        + T X Y Z (nabla.curvature U V W) p := by
  have dir_sub_smooth (Q : SmoothVectorField I M) {f h : M → ℝ} (q : M)
      (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) :
      Q.dir (fun r => f r - h r) q = Q.dir f q - Q.dir h q := by
    simp only [SmoothVectorField.dir]
    rw [show (fun r => f r - h r) = f - h from rfl,
      mfderiv_sub (hf.mdifferentiableAt (by simp))
        (hh.mdifferentiableAt (by simp))]
    rfl
  have hdirCov (Q A B C D R : SmoothVectorField I M) :
      Q.dir (MorganTianLib.covariantDifferential4 nabla T A B C D R) p =
        Q.dir (R.dir (T A B C D)) p
          - Q.dir (T (nabla.cov R A) B C D) p
          - Q.dir (T A (nabla.cov R B) C D) p
          - Q.dir (T A B (nabla.cov R C) D) p
          - Q.dir (T A B C (nabla.cov R D)) p := by
    have h0 := R.dir_contMDiff (hsm A B C D)
    have h1 := hsm (nabla.cov R A) B C D
    have h2 := hsm A (nabla.cov R B) C D
    have h3 := hsm A B (nabla.cov R C) D
    have h4 := hsm A B C (nabla.cov R D)
    change Q.dir (fun q => R.dir (T A B C D) q
      - T (nabla.cov R A) B C D q
      - T A (nabla.cov R B) C D q
      - T A B (nabla.cov R C) D q
      - T A B C (nabla.cov R D) q) p = _
    rw [dir_sub_smooth Q p (((h0.sub h1).sub h2).sub h3) h4,
      dir_sub_smooth Q p ((h0.sub h1).sub h2) h3,
      dir_sub_smooth Q p (h0.sub h1) h2,
      dir_sub_smooth Q p h0 h1]
  have hbase :
      U.dir (V.dir (T X Y Z W)) p - (nabla.cov U V).dir (T X Y Z W) p =
        V.dir (U.dir (T X Y Z W)) p - (nabla.cov V U).dir (T X Y Z W) p := by
    simpa only [MorganTianLib.hessian] using
      (MorganTianLib.hessian_symm nabla hsym (hsm X Y Z W) U V p)
  have hbr : bracketField U V = nabla.cov U V - nabla.cov V U := by
    ext q
    rw [SmoothVectorField.sub_apply, bracketField_apply]
    exact (hsym U V q).symm
  have hcurv (A : SmoothVectorField I M) :
      nabla.curvature U V A =
        (nabla.cov V (nabla.cov U A) - nabla.cov U (nabla.cov V A))
          + (nabla.cov (nabla.cov U V) A - nabla.cov (nabla.cov V U) A) := by
    ext q
    simp only [nabla.curvature_apply, hbr, nabla.cov_sub_left,
      SmoothVectorField.add_apply, SmoothVectorField.sub_apply]
  have hslot (S : SmoothVectorField I M → M → ℝ)
      (hadd : ∀ A B q, S (A + B) q = S A q + S B q)
      (A : SmoothVectorField I M) :
      (S (nabla.cov V (nabla.cov U A)) p
          - S (nabla.cov U (nabla.cov V A)) p)
        + (S (nabla.cov (nabla.cov U V) A) p
          - S (nabla.cov (nabla.cov V U) A) p)
        = S (nabla.curvature U V A) p := by
    symm
    calc
      S (nabla.curvature U V A) p =
          S ((nabla.cov V (nabla.cov U A) - nabla.cov U (nabla.cov V A))
            + (nabla.cov (nabla.cov U V) A - nabla.cov (nabla.cov V U) A)) p := by
              rw [hcurv A]
      _ = S (nabla.cov V (nabla.cov U A) - nabla.cov U (nabla.cov V A)) p
          + S (nabla.cov (nabla.cov U V) A - nabla.cov (nabla.cov V U) A) p :=
            hadd _ _ p
      _ = _ := by
        rw [MorganTianLib.tensorial_sub_apply S hadd
              (nabla.cov V (nabla.cov U A)) (nabla.cov U (nabla.cov V A)) p,
          MorganTianLib.tensorial_sub_apply S hadd
              (nabla.cov (nabla.cov U V) A) (nabla.cov (nabla.cov V U) A) p]
  have hX := hslot (fun A => T A Y Z W)
    (fun A B q => hT.add₁ A B Y Z W q) X
  have hY := hslot (fun A => T X A Z W)
    (fun A B q => hT.add₂ X A B Z W q) Y
  have hZ := hslot (fun A => T X Y A W)
    (fun A B q => hT.add₃ X Y A B W q) Z
  have hW := hslot (fun A => T X Y Z A)
    (fun A B q => hT.add₄ X Y Z A B q) W
  change
    (U.dir (MorganTianLib.covariantDifferential4 nabla T X Y Z W V) p
      - MorganTianLib.covariantDifferential4 nabla T (nabla.cov U X) Y Z W V p
      - MorganTianLib.covariantDifferential4 nabla T X (nabla.cov U Y) Z W V p
      - MorganTianLib.covariantDifferential4 nabla T X Y (nabla.cov U Z) W V p
      - MorganTianLib.covariantDifferential4 nabla T X Y Z (nabla.cov U W) V p
      - MorganTianLib.covariantDifferential4 nabla T X Y Z W (nabla.cov U V) p)
    - (V.dir (MorganTianLib.covariantDifferential4 nabla T X Y Z W U) p
      - MorganTianLib.covariantDifferential4 nabla T (nabla.cov V X) Y Z W U p
      - MorganTianLib.covariantDifferential4 nabla T X (nabla.cov V Y) Z W U p
      - MorganTianLib.covariantDifferential4 nabla T X Y (nabla.cov V Z) W U p
      - MorganTianLib.covariantDifferential4 nabla T X Y Z (nabla.cov V W) U p
      - MorganTianLib.covariantDifferential4 nabla T X Y Z W (nabla.cov V U) p) = _
  rw [hdirCov U X Y Z W V, hdirCov V X Y Z W U]
  simp only [MorganTianLib.covariantDifferential4]
  linear_combination hbase + hX + hY + hZ + hW

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** A tuple representation of a smooth covariant `4`-tensor has a
pointwise multilinear covariant derivative. -/
theorem isPointwiseMultilinear_covDerivAlong_four
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ))
    (hT : IsCovariantTensor4 T)
    (hsm : ∀ X Y Z W, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y Z W))
    (A : CovTensorField I M 4)
    (hA : ∀ (Y : Fin 4 → SmoothVectorField I M) (q : M),
      A Y q = T (Y 0) (Y 1) (Y 2) (Y 3) q)
    (U : SmoothVectorField I M) (p : M) :
    IsPointwiseMultilinear (covDerivAlong nabla U A) p := by
  refine isPointwiseMultilinear_of_isCovariantTensor4
    (fun X Y Z W => MorganTianLib.covariantDifferential4 nabla T X Y Z W U)
    (isCovariantTensor4_covariantDifferential4 nabla T hT hsm U)
    (covDerivAlong nabla U A) ?_ p
  intro Y q
  exact covDerivAlong_eq_covariantDifferential4 nabla T A hA U Y q

/-! ### The Riemann tensor -/

/-- **Math.** **`\Rm` is pointwise multilinear.** The Riemann tensor as a
covariant `4`-tensor field reads only the arguments' values at `p`, and
`riemannCurvatureAt g p` is additive and homogeneous in each of its four slots —
that is `IsAlgCurvatureForm`'s content (`add_left`/`add_two`/`add_three`/
`add_four` and the four `smul_*`), which `riemannCurvatureAt_isAlg` supplies.

This is the witness the frame results need in order to say anything about
`|\Rm|²`: without it `normSqAt_eq_sum_of_frame` is a theorem about an empty
class. -/
theorem isPointwiseMultilinear_riemannTensorField (g : RiemannianMetric I M)
    (p : M) : IsPointwiseMultilinear (riemannTensorField g) p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have halg := riemannCurvatureAt_isAlg g p
  refine isPointwiseMultilinear_of_pointwise
    (fun v => riemannCurvatureAt g p (v 0) (v 1) (v 2) (v 3))
    (fun Y => rfl) ?_ ?_
  · intro i v x y
    fin_cases i <;> simp only [Fin.isValue, Function.update] <;> norm_num
    · exact halg.add_left _ _ _ _ _
    · exact halg.add_two _ _ _ _ _
    · exact halg.add_three _ _ _ _ _
    · exact halg.add_four _ _ _ _ _
  · intro i v c x
    fin_cases i <;> simp only [Fin.isValue, Function.update] <;> norm_num
    · exact halg.smul_left _ _ _ _ _
    · exact halg.smul_two _ _ _ _ _
    · exact halg.smul_three _ _ _ _ _
    · exact halg.smul_four _ _ _ _ _

/-- **Math.** **`nabla_U Rm` is pointwise multilinear.** This is the genuine
tensoriality producer needed by the curvature-norm Leibniz and Bochner
identities; it has no tensoriality hypothesis of its own. -/
theorem isPointwiseMultilinear_covDerivAlong_riemannTensorField
    (g : RiemannianMetric I M) (U : SmoothVectorField I M) (p : M) :
    IsPointwiseMultilinear
      (covDerivAlong g.leviCivitaConnection U (riemannTensorField g)) p := by
  refine isPointwiseMultilinear_covDerivAlong_four g.leviCivitaConnection
    (g.leviCivitaConnection.curvatureForm g)
    (g.leviCivitaConnection.curvatureForm_isCovariantTensor4 g)
    (fun X Y Z W => MorganTianLib.curvatureForm_contMDiff
      g g.leviCivitaConnection X Y Z W)
    (riemannTensorField g) ?_ U p
  intro Y q
  exact riemannCurvatureAt_eq g q rfl rfl rfl rfl

/-- **Math.** The second covariant derivative of `Rm` is the corrected iterated
covariant differential of the curvature form. -/
theorem secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
    (g : RiemannianMetric I M) (U V : SmoothVectorField I M)
    (Y : Fin 4 → SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection U V
        (riemannTensorField g) Y p =
      MorganTianLib.covariantDifferential4 g.leviCivitaConnection
          (fun X Y Z W =>
            MorganTianLib.covariantDifferential4 g.leviCivitaConnection
              (g.leviCivitaConnection.curvatureForm g) X Y Z W V)
          (Y 0) (Y 1) (Y 2) (Y 3) U p
        - MorganTianLib.covariantDifferential4 g.leviCivitaConnection
            (g.leviCivitaConnection.curvatureForm g)
            (Y 0) (Y 1) (Y 2) (Y 3)
            (g.leviCivitaConnection.cov U V) p := by
  exact secondCovDerivAlong_eq_iteratedCovariantDifferential4
    g.leviCivitaConnection
    (g.leviCivitaConnection.curvatureForm g)
    (riemannTensorField g)
    (fun Z q => riemannCurvatureAt_eq g q rfl rfl rfl rfl)
    U V Y p

/-- **Math.** The corrected second covariant derivatives of `Rm` commute up to
the sum of the four curvature actions on `Rm`.  This is the rank-four Ricci
commutator used in the curvature-Laplacian calculation. -/
theorem secondCovDerivAlong_riemannTensorField_sub_swap
    (g : RiemannianMetric I M) (U V : SmoothVectorField I M)
    (Y : Fin 4 → SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection U V
        (riemannTensorField g) Y p
      - secondCovDerivAlong g.leviCivitaConnection V U
          (riemannTensorField g) Y p =
      g.leviCivitaConnection.curvatureForm g
          (g.leviCivitaConnection.curvature U V (Y 0)) (Y 1) (Y 2) (Y 3) p
        + g.leviCivitaConnection.curvatureForm g
            (Y 0) (g.leviCivitaConnection.curvature U V (Y 1)) (Y 2) (Y 3) p
        + g.leviCivitaConnection.curvatureForm g
            (Y 0) (Y 1) (g.leviCivitaConnection.curvature U V (Y 2)) (Y 3) p
        + g.leviCivitaConnection.curvatureForm g
            (Y 0) (Y 1) (Y 2)
            (g.leviCivitaConnection.curvature U V (Y 3)) p := by
  rw [secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
      g U V Y p,
    secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
      g V U Y p]
  exact correctedIteratedCovariantDifferential4_sub_swap
    g.leviCivitaConnection (isLeviCivita_leviCivitaConnection g).1
    (g.leviCivitaConnection.curvatureForm g)
    (g.leviCivitaConnection.curvatureForm_isCovariantTensor4 g)
    (fun X Y Z W => MorganTianLib.curvatureForm_contMDiff
      g g.leviCivitaConnection X Y Z W)
    (Y 0) (Y 1) (Y 2) (Y 3) U V p

/-- **Math.** **An iterated derivative `nabla_V nabla_U Rm` is pointwise
multilinear in the four curvature slots.** The first covariant differential is
a smooth covariant four-tensor, so the same unconditional producer applies a
second time. -/
theorem isPointwiseMultilinear_covDerivAlong_covDerivAlong_riemannTensorField
    (g : RiemannianMetric I M) (U V : SmoothVectorField I M) (p : M) :
    IsPointwiseMultilinear
      (covDerivAlong g.leviCivitaConnection V
        (covDerivAlong g.leviCivitaConnection U (riemannTensorField g))) p := by
  let T := g.leviCivitaConnection.curvatureForm g
  let dT := fun X Y Z W =>
    MorganTianLib.covariantDifferential4 g.leviCivitaConnection T X Y Z W U
  have hT : IsCovariantTensor4 T :=
    g.leviCivitaConnection.curvatureForm_isCovariantTensor4 g
  have hsm : ∀ X Y Z W, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y Z W) :=
    fun X Y Z W => MorganTianLib.curvatureForm_contMDiff
      g g.leviCivitaConnection X Y Z W
  refine isPointwiseMultilinear_covDerivAlong_four g.leviCivitaConnection dT
    (isCovariantTensor4_covariantDifferential4 g.leviCivitaConnection T hT hsm U)
    (fun X Y Z W => covariantDifferential4_contMDiff
      g.leviCivitaConnection T hsm X Y Z W U)
    (covDerivAlong g.leviCivitaConnection U (riemannTensorField g)) ?_ V p
  intro Y q
  exact covDerivAlong_eq_covariantDifferential4 g.leviCivitaConnection T
    (riemannTensorField g) (fun Z r => riemannCurvatureAt_eq g r rfl rfl rfl rfl)
    U Y q

/-! ### The Ricci tensor and the metric -/

/-- **Math.** **`\Ric` is pointwise multilinear**: `ricciTensorAt g p` is by
construction an element of `T_pM →ₗ[ℝ] T_pM →ₗ[ℝ] ℝ`, so both slots are linear,
and `ricciTensorField` reads only the values at `p`. -/
theorem isPointwiseMultilinear_ricciTensorField (g : RiemannianMetric I M)
    (p : M) : IsPointwiseMultilinear (ricciTensorField g) p := by
  classical
  refine isPointwiseMultilinear_of_pointwise
    (fun v => ricciTensorAt g p (v 0) (v 1)) (fun Y => rfl) ?_ ?_
  · intro i v x y
    fin_cases i <;> simp only [Fin.isValue, Function.update] <;> norm_num
  · intro i v c x
    fin_cases i <;> simp only [Fin.isValue, Function.update] <;> norm_num

/-- **Math.** The two-field presentation of `Ric` is a genuine covariant
`2`-tensor, directly from the bilinearity of `ricciTensorAt`. -/
theorem isCovariantTensor2_ricciTensorField (g : RiemannianMetric I M) :
    IsCovariantTensor2
      (fun X Y q => ricciTensorAt g q (X q) (Y q)) where
  add_left X₁ X₂ Y q := by
    rw [SmoothVectorField.add_apply, map_add, LinearMap.add_apply]
  add_right X Y₁ Y₂ q := by
    rw [SmoothVectorField.add_apply, map_add]
  smul_left f hf X Y q := by
    rw [SmoothVectorField.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  smul_right f hf X Y q := by
    rw [SmoothVectorField.smul_apply, map_smul, smul_eq_mul]

/-- **Math.** **`nabla_U Ric` is pointwise multilinear.** The Ricci tensor's
two-field presentation is smooth and covariant, so the rank-two differential
producer applies without an auxiliary tensoriality hypothesis. -/
theorem isPointwiseMultilinear_covDerivAlong_ricciTensorField
    (g : RiemannianMetric I M) (U : SmoothVectorField I M) (p : M) :
    IsPointwiseMultilinear
      (covDerivAlong g.leviCivitaConnection U (ricciTensorField g)) p := by
  let T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ) :=
    fun X Y q => ricciTensorAt g q (X q) (Y q)
  have hT : IsCovariantTensor2 T := isCovariantTensor2_ricciTensorField g
  have hsm : ∀ X Y, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y) := by
    intro X Y
    have h := hasSmoothComponents_ricciTensorField g
      (fun i => if i = 0 then X else Y)
    have hfun : ricciTensorField g (fun i => if i = 0 then X else Y) =
        fun q => T X Y q := by
      funext q
      rw [ricciTensorField]
      simp [T]
    rw [hfun] at h
    exact h
  have hA : ∀ (Y : Fin 2 → SmoothVectorField I M) (q : M),
      ricciTensorField g Y q = T (Y 0) (Y 1) q := by
    intro Y q
    rfl
  exact isPointwiseMultilinear_covDerivAlong_two
    g.leviCivitaConnection T hT hsm (ricciTensorField g) hA U p

/-- **Math.** The second covariant derivative of `Ric` is the corrected
iterated covariant differential of its two-field presentation. -/
theorem secondCovDerivAlong_ricciTensorField_eq_iteratedCovariantDifferential2
    (g : RiemannianMetric I M) (U V : SmoothVectorField I M)
    (Y : Fin 2 → SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection U V
        (ricciTensorField g) Y p =
      g.leviCivitaConnection.covariantDifferential2
          (fun X Y => g.leviCivitaConnection.covariantDifferential2
            (fun A B q => ricciTensorAt g q (A q) (B q)) X Y V)
          (Y 0) (Y 1) U p
        - g.leviCivitaConnection.covariantDifferential2
            (fun A B q => ricciTensorAt g q (A q) (B q))
            (Y 0) (Y 1) (g.leviCivitaConnection.cov U V) p := by
  exact secondCovDerivAlong_eq_iteratedCovariantDifferential2
    g.leviCivitaConnection
    (fun A B q => ricciTensorAt g q (A q) (B q))
    (ricciTensorField g) (fun Z q => rfl) U V Y p

/-- **Math.** The corrected second covariant derivatives of `Ric` commute up to
the two positive curvature actions in its covariant slots. -/
theorem secondCovDerivAlong_ricciTensorField_sub_swap
    (g : RiemannianMetric I M) (U V : SmoothVectorField I M)
    (Y : Fin 2 → SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection U V
        (ricciTensorField g) Y p
      - secondCovDerivAlong g.leviCivitaConnection V U
          (ricciTensorField g) Y p =
      ricciTensorAt g p
          ((g.leviCivitaConnection.curvature U V (Y 0)) p) (Y 1 p)
        + ricciTensorAt g p (Y 0 p)
            ((g.leviCivitaConnection.curvature U V (Y 1)) p) := by
  rw [secondCovDerivAlong_ricciTensorField_eq_iteratedCovariantDifferential2
      g U V Y p,
    secondCovDerivAlong_ricciTensorField_eq_iteratedCovariantDifferential2
      g V U Y p]
  apply correctedIteratedCovariantDifferential2_sub_swap
    g.leviCivitaConnection (isLeviCivita_leviCivitaConnection g).1
    (fun A B q => ricciTensorAt g q (A q) (B q))
    (isCovariantTensor2_ricciTensorField g)
  intro X Z
  have hsm := hasSmoothComponents_ricciTensorField g
    (fun i => if i = 0 then X else Z)
  have hfun : ricciTensorField g (fun i => if i = 0 then X else Z) =
      fun q => ricciTensorAt g q (X q) (Z q) := by
    funext q
    rw [ricciTensorField]
    simp
  rw [hfun] at hsm
  exact hsm

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** **The metric is pointwise multilinear**, by bilinearity of
`metricInner`. Needed because `tr₁₂` of `g`-multiples appears throughout the
gravitation-tensor computations. -/
theorem isPointwiseMultilinear_metricTensorField (g : RiemannianMetric I M)
    (p : M) : IsPointwiseMultilinear (metricTensorField g) p := by
  classical
  refine isPointwiseMultilinear_of_pointwise
    (fun v => g.metricInner p (v 0) (v 1)) (fun Y => rfl) ?_ ?_
  · intro i v x y
    fin_cases i <;> simp only [Fin.isValue, Function.update] <;>
      norm_num [g.metricInner_add_left, g.metricInner_add_right]
  · intro i v c x
    fin_cases i <;> simp only [Fin.isValue, Function.update] <;>
      norm_num [g.metricInner_smul_left, g.metricInner_smul_right]

/-! ### The payoff: `|\Rm|²` and `|\Ric|²` over a smooth frame -/

/-- **Math.** **`|\Rm|²` is a finite sum of squares of smooth-frame components
near every point.** Combining the `\Rm` witness with
`exists_smooth_frame_normSqAt`: there are global smooth vector fields
`F₁,…,F_n` and a neighbourhood of `p` on which
`|\Rm|²(q) = Σ_{ijkl} \Rm(F_i,F_j,F_k,F_l)(q)²`.

No per-point basis remains, so the regularity of `|\Rm|²` is that of the
component functions `\Rm(F_i,F_j,F_k,F_l)`. This is the unconditional form of
what the curvature Bochner identity needs (I-0494). -/
theorem exists_smooth_frame_riemannNormSq (g : RiemannianMetric I M) (p : M) :
    ∃ F : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      ∀ᶠ q in 𝓝 p, normSqAt g (riemannTensorField g) q
        = ∑ v : Fin 4 → Fin (Module.finrank ℝ E),
            riemannTensorField g (fun j => F (v j)) q ^ 2 := by
  obtain ⟨F, hF⟩ := exists_smooth_frame_normSqAt g (riemannTensorField g) p
  exact ⟨F, hF.mono fun q hq =>
    hq (isPointwiseMultilinear_riemannTensorField g q)⟩

/-- **Math.** The same for `|\Ric|²`. -/
theorem exists_smooth_frame_ricciNormSq (g : RiemannianMetric I M) (p : M) :
    ∃ F : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      ∀ᶠ q in 𝓝 p, normSqAt g (ricciTensorField g) q
        = ∑ v : Fin 2 → Fin (Module.finrank ℝ E),
            ricciTensorField g (fun j => F (v j)) q ^ 2 := by
  obtain ⟨F, hF⟩ := exists_smooth_frame_normSqAt g (ricciTensorField g) p
  exact ⟨F, hF.mono fun q hq =>
    hq (isPointwiseMultilinear_ricciTensorField g q)⟩

#print axioms Topping.isPointwiseMultilinear_covDerivAlong_riemannTensorField
#print axioms Topping.isPointwiseMultilinear_covDerivAlong_covDerivAlong_riemannTensorField
#print axioms Topping.secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
#print axioms Topping.correctedIteratedCovariantDifferential4_sub_swap
#print axioms Topping.secondCovDerivAlong_riemannTensorField_sub_swap
#print axioms Topping.isCovariantTensor2_ricciTensorField
#print axioms Topping.isPointwiseMultilinear_covDerivAlong_ricciTensorField
#print axioms Topping.correctedIteratedCovariantDifferential2_sub_swap
#print axioms Topping.secondCovDerivAlong_ricciTensorField_sub_swap

end Topping

end
