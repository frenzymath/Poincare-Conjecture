import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.DerivationBundle
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import LeeSmoothLib.Ch08.Sec08_54.Definition_8_54_extra_1
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

section

universe u𝕜 uE uH uM

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "SmoothFunction" => C^∞⟮I, M; 𝕜⟯
local notation "SmoothDerivation" => Derivation 𝕜 SmoothFunction SmoothFunction
local notation "SmoothVectorField" => Cₛ^∞⟮I; E, fun p : M ↦ TangentSpace I p⟯

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so the bridge
-- below was matched directly against the `ContMDiffSection` owner namespace for bundled smooth
-- sections and mathlib's `Derivation`/`PointDerivation` API for smooth functions.

/-- Pointwise application of a bundled smooth vector field to a smooth function is again smooth. -/
theorem ContMDiffSection.contMDiff_apply
    (X : SmoothVectorField) (f : SmoothFunction) :
    ContMDiff I 𝓘(𝕜) ∞ (VectorField.apply X f) := by
  -- Route correction: instead of matching `mfderiv_const` directly against the hom-bundle
  -- coordinates, factor through the smooth tangent map of `f` and then read its fiber coordinate.
  have hX : ContMDiff I I.tangent ∞ (T% fun p => X p) := X.contMDiff
  have hTangent :
      ContMDiff I (𝓘(𝕜).tangent) ∞ (tangentMap I 𝓘(𝕜) (f : M → 𝕜) ∘ (T% fun p => X p)) := by
    -- The tangent map of a smooth scalar-valued function is smooth on the tangent bundle.
    exact (f.contMDiff.contMDiff_tangentMap (m := ∞) (n := ∞) (by simp)).comp hX
  have hSnd :
      ContMDiff (𝓘(𝕜).tangent) 𝓘(𝕜) ∞ (fun p : TangentBundle 𝓘(𝕜) 𝕜 => p.2) :=
    contMDiff_snd_tangentBundle_modelSpace (H := 𝕜) (I := 𝓘(𝕜)) (n := ∞)
  -- The fiber coordinate of the composed tangent map is exactly `VectorField.apply X f`.
  simpa [Function.comp, VectorField.apply_def, tangentMap_snd] using hSnd.comp hTangent

namespace ContMDiffSection

/-- Applying a bundled smooth vector field to a smooth function gives the corresponding bundled
smooth scalar-valued function. -/
def apply (X : SmoothVectorField) (f : SmoothFunction) : SmoothFunction :=
  ⟨VectorField.apply X f, X.contMDiff_apply f⟩

/-- Applying a smooth vector field to a sum of smooth functions is additive. -/
theorem apply_add
    (X : SmoothVectorField) (f g : SmoothFunction) :
    X.apply (f + g) = X.apply f + X.apply g := by
  ext x
  -- Reduce the bundled equality to the pointwise derivative-of-sum formula at `x`.
  have hf : MDiffAt f x := f.contMDiff.mdifferentiableAt (by simp)
  have hg : MDiffAt g x := g.contMDiff.mdifferentiableAt (by simp)
  simpa [ContMDiffSection.apply, VectorField.apply_def] using
    congrArg (fun L => L (X x)) (mfderiv_add hf hg)

/-- Applying a smooth vector field to a scalar multiple of a smooth function is `𝕜`-linear. -/
theorem apply_smul
    (X : SmoothVectorField) (c : 𝕜) (f : SmoothFunction) :
    X.apply (c • f) = c • X.apply f := by
  ext x
  -- Reduce the bundled equality to the pointwise derivative of a constant scalar multiple.
  have hf : MDiffAt f x := f.contMDiff.mdifferentiableAt (by simp)
  simpa [ContMDiffSection.apply, VectorField.apply_def, smul_eq_mul] using
    congrArg (fun L => L (X x)) (const_smul_mfderiv hf c)

/-- Applying a smooth vector field to a product of smooth functions satisfies the Leibniz rule. -/
theorem apply_mul
    (X : SmoothVectorField) (f g : SmoothFunction) :
    X.apply (f * g) = f • X.apply g + g • X.apply f := by
  ext x
  -- Reduce to the pointwise product rule, then normalize scalar multiplication on smooth
  -- functions to the usual commutative-ring expression.
  have hf : MDiffAt f x := f.contMDiff.mdifferentiableAt (by simp)
  have hg : MDiffAt g x := g.contMDiff.mdifferentiableAt (by simp)
  simpa [ContMDiffSection.apply, VectorField.apply_def, PointedContMDiffMap.smul_def,
    smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using
    fromTangentSpace_mfderiv_smul_apply hf hg (X x)

/-- Notation 8.56-extra-3: a bundled smooth vector field on `M` determines the corresponding
derivation of `C^∞(M, 𝕜)` obtained by applying each tangent vector `X x` pointwise to smooth
`𝕜`-valued functions. -/
def toDerivation (X : SmoothVectorField) : SmoothDerivation :=
  Derivation.mk'
    { toFun := X.apply
      map_add' := X.apply_add
      map_smul' := X.apply_smul }
    (X.apply_mul)

/-- Evaluating the derivation associated to a smooth vector field is pointwise directional
differentiation, matching `TangentSpace.toPointDerivation_apply` at each point. -/
theorem toDerivation_apply (X : SmoothVectorField) (f : SmoothFunction) (x : M) :
    X.toDerivation f x = VectorField.apply X f x :=
  rfl

end ContMDiffSection

end
