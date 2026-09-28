/-
Chapter 2, "Riemannian Metrics", §"Raising and Lowering Indices": the musical
isomorphisms and the gradient.

Lee defines a bundle homomorphism `g̃ : TM → T*M` by `g̃(v)(w) = g_p(v,w)`, writes
`v^♭ = g̃(v)` ("`v` flat", *lowering an index*), observes that `g̃` is invertible
because the matrix `(g_ij)` is nonsingular at each point, and writes
`α^♯ = g̃⁻¹(α)` ("`α` sharp", *raising an index*).  The gradient of a smooth
`f : M → ℝ` is then `grad f = (df)^♯`, characterized by Lee's (2.14):

  `df_p(w) = ⟨grad f|_p, w⟩`  for all `p ∈ M`, `w ∈ T_p M`.

Two remarks on how this is set up here.

* **Flat is not new data.**  `g̃(v)(w) = g_p(v,w)` says exactly that `g̃|_p` is
  `g.inner p`, which is already a continuous linear map `T_p M →L[ℝ] (T_p M →L[ℝ] ℝ)`.
  So `flat` below is a wrapper on `g.inner`, and `flat_apply` is `rfl`.  The
  content of the section is not the definition of `♭` but its *invertibility*.

* **Invertibility is Riesz representation, not a matrix inverse.**  Lee argues
  that `(g_ij)` is nonsingular; the formal route instead installs the fibrewise
  inner product coming from `g` (mathlib's `RiemannianBundle`) and uses
  `InnerProductSpace.toDual`, the Riesz isomorphism `E ≃ₗᵢ E*`, which *is* `♭`
  by construction and comes with its inverse already built.  This needs the
  fibres to be complete, which in Lee's standing finite-dimensional setting is
  automatic — hence the `[FiniteDimensional ℝ E]` hypothesis throughout.

Everything here is pointwise/fibrewise.  Lee also asserts that `♭` and `♯` are
*smooth* bundle homomorphisms and that `grad f` is a *smooth vector field*;
those statements need `T*M` as a bundle in its own right, which the pinned
mathlib does not have (there is no `CotangentBundle`), and are left to a later
session.  The pointwise theory below is what Lee's Proposition 2.37 and his
hypersurface results actually consume.
-/
import LeeLib.Ch02.RiemannianMetric
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace LeeLib.Ch02

open Bundle Manifold
open scoped Manifold ContDiff

section Musical

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable (g : RiemannianMetric I M) (p : M)

/-- **The flat map** `♭ : T_p M → T_p^* M` (Lee, §"Raising and Lowering
Indices"): `v^♭ = g_p(v, ·)`, the covector obtained from `v` by *lowering an
index*.

This is `g.inner p` under a different name: Lee's defining equation
`g̃(v)(w) = g_p(v,w)` is exactly the statement that `g̃|_p` is the bilinear form
`g_p` read as a map into the dual. -/
noncomputable def flat : TangentSpace I p →L[ℝ] (TangentSpace I p →L[ℝ] ℝ) := g.inner p

omit [FiniteDimensional ℝ E] in
@[simp] theorem flat_apply (v w : TangentSpace I p) : flat g p v w = g.innerAt p v w := rfl

omit [FiniteDimensional ℝ E] in
/-- The fibrewise inner product installed by `RiemannianBundle` is `g.inner`. -/
theorem inner_eq_innerAt (v w : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    (inner ℝ v w : ℝ) = g.innerAt p v w := rfl

/-- **The sharp map** `♯ : T_p^* M → T_p M` (Lee, §"Raising and Lowering
Indices"): `α^♯` is the vector obtained from the covector `α` by *raising an
index*, i.e. the unique `v` with `g_p(v, ·) = α`.

Lee inverts the matrix `(g_ij)`; formally this is the Riesz representation
isomorphism `InnerProductSpace.toDual` for the inner product that `g` installs
on `T_p M`, whose inverse is already available.  `flat_sharp` and `sharp_flat`
below record that `♯` is indeed inverse to `♭`. -/
noncomputable def sharp (a : TangentSpace I p →L[ℝ] ℝ) : TangentSpace I p :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  (InnerProductSpace.toDual ℝ (TangentSpace I p)).symm a

/-- **The defining property of `♯`**: `g_p(α^♯, w) = α(w)` for every `w`.

This is Lee's characterization of raising an index, and the fibrewise form of
his (2.14). -/
@[simp] theorem innerAt_sharp (a : TangentSpace I p →L[ℝ] ℝ) (w : TangentSpace I p) :
    g.innerAt p (sharp g p a) w = a w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  show (inner ℝ (sharp g p a) w : ℝ) = a w
  exact InnerProductSpace.toDual_symm_apply

/-- `♯` is a left inverse of `♭`: raising the index of `v^♭` returns `v`. -/
@[simp] theorem sharp_flat (v : TangentSpace I p) : sharp g p (flat g p v) = v := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  exact (InnerProductSpace.toDual ℝ (TangentSpace I p)).symm_apply_apply v

/-- `♯` is a right inverse of `♭`: lowering the index of `α^♯` returns `α`. -/
@[simp] theorem flat_sharp (a : TangentSpace I p →L[ℝ] ℝ) : flat g p (sharp g p a) = a :=
  ContinuousLinearMap.ext fun w => innerAt_sharp g p a w

/-- **The musical isomorphisms are mutually inverse bijections** — Lee's
statement that `g̃` is invertible with inverse `g̃⁻¹`, so that `♭` and `♯` are
inverse to one another. -/
theorem flat_bijective : Function.Bijective (flat g p) :=
  ⟨Function.LeftInverse.injective (sharp_flat g p),
    Function.RightInverse.surjective (flat_sharp g p)⟩

/-- `♭` is injective: distinct vectors have distinct associated covectors. This
is the fibrewise nondegeneracy of `g`. -/
theorem flat_injective : Function.Injective (flat g p) := (flat_bijective g p).1

end Musical

/-! ### The gradient -/

section Gradient

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable (g : RiemannianMetric I M) (f : M → ℝ) (p : M)

/-- **The gradient of a smooth function** (Lee, §"Raising and Lowering
Indices"): `grad f = (df)^♯`, the vector field obtained from the differential
`df` by raising an index.

Lee calls this "probably the most important application of the sharp operator":
it is what extends the classical gradient to a Riemannian manifold.  The
differential `df_p` is mathlib's `extDerivFun`, the exterior derivative of a
scalar function as a covector at each point. -/
noncomputable def grad : TangentSpace I p := sharp g p (extDerivFun (I := I) f p)

/-- **Lee's (2.14)**: the gradient is characterized by
`df_p(w) = ⟨grad f|_p, w⟩` for every `w ∈ T_p M`.

Lee obtains this by "unwinding the definitions", and so does the proof: it is
the defining property of `♯` applied to `df_p`. -/
@[simp] theorem innerAt_grad (w : TangentSpace I p) :
    g.innerAt p (grad g f p) w = extDerivFun (I := I) f p w :=
  innerAt_sharp g p _ w

/-- The gradient is the unique vector representing `df_p` under `g` — the
uniqueness implicit in Lee's (2.14), which follows from nondegeneracy of `g`. -/
theorem eq_grad_of_innerAt (v : TangentSpace I p)
    (hv : ∀ w : TangentSpace I p, g.innerAt p v w = extDerivFun (I := I) f p w) :
    v = grad g f p :=
  flat_injective g p (ContinuousLinearMap.ext fun w => (hv w).trans (innerAt_grad g f p w).symm)

/-- **The gradient is orthogonal to the kernel of the differential.**

This is the pointwise heart of Lee's Proposition 2.37 ("`grad f` is everywhere
normal to the regular level set `M_c`"): the tangent space to a level set of `f`
at `p` is `ker df_p`, and `grad f|_p` is `g`-orthogonal to it.  Stated here
directly in terms of `ker df_p`, which needs no submanifold machinery — Lee's
identification of `ker df_p` with `T_p M_c` is what Corollary A.26 supplies, and
is the only part of Proposition 2.37 still outstanding. -/
theorem innerAt_grad_eq_zero_of_mem_ker (w : TangentSpace I p)
    (hw : mfderiv I 𝓘(ℝ, ℝ) f p w = 0) : g.innerAt p (grad g f p) w = 0 := by
  rw [innerAt_grad]
  show (NormedSpace.fromTangentSpace (f p)).toContinuousLinearMap (mfderiv I 𝓘(ℝ, ℝ) f p w) = 0
  rw [hw, map_zero]

/-- At a critical point of `f` (where `df_p = 0`) the gradient vanishes, and
conversely.  Lee calls `p` a *regular point* of `f` when `df_p ≠ 0` and a
*critical point* otherwise, so this says the regular points of `f` are exactly
the points where `grad f` does not vanish. -/
theorem grad_eq_zero_iff : grad g f p = 0 ↔ extDerivFun (I := I) f p = 0 := by
  constructor
  · intro h
    refine ContinuousLinearMap.ext fun w => ?_
    rw [← innerAt_grad g f p w, h]
    simp [RiemannianMetric.innerAt]
  · intro h
    refine flat_injective g p (ContinuousLinearMap.ext fun w => ?_)
    rw [flat_apply, innerAt_grad, h]
    simp

end Gradient

end LeeLib.Ch02
