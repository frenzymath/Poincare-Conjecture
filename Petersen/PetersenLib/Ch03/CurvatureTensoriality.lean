import PetersenLib.Ch03.CurvatureTensor

/-!
# Petersen Ch. 3, §3.1 — full tensoriality of the curvature tensor

`C^∞(M)`-linearity of `R(X,Y)Z` in its first two slots
(`curvatureTensor_add_first`, `curvatureTensor_smul_first`,
`curvatureTensor_add_middle`, `curvatureTensor_smul_middle`), complementing the
`Z`-slot tensoriality of `curvatureTensor_tensorial`, together with locality:
the value `R(X,Y)Z|_p` only depends on the germs of the three fields at `p`
(`curvatureTensor_congr_first`, `curvatureTensor_congr_middle`,
`curvatureTensor_congr_field`). These are the inputs for the pointwise
curvature tensor of §3.1.3.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.
-/

open Bundle Set Function Finset Filter
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Additivity and `C^∞`-homogeneity in the first two slots -/

section Homogeneity

variable [CompleteSpace E]

/-- `R(X₁ + X₂, Y)Z = R(X₁,Y)Z + R(X₂,Y)Z` for smooth fields. -/
theorem curvatureTensor_add_first (D : AffineConnection I M)
    {X₁ X₂ Y Z : Π x : M, TangentSpace I x}
    (hX₁ : IsSmoothVectorField X₁) (hX₂ : IsSmoothVectorField X₂)
    (hZ : IsSmoothVectorField Z) (p : M) :
    curvatureTensor D (fun q => X₁ q + X₂ q) Y Z p
      = curvatureTensor D X₁ Y Z p + curvatureTensor D X₂ Y Z p := by
  have hX₁' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, X₁ q⟩ : TangentBundle I M)) p :=
    (hX₁ p).mdifferentiableAt (by decide)
  have hX₂' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, X₂ q⟩ : TangentBundle I M)) p :=
    (hX₂ p).mdifferentiableAt (by decide)
  -- the covariant derivative in the direction of the sum field
  have hcf : D.covField (fun q => X₁ q + X₂ q) Z
      = fun q => D.covField X₁ Z q + D.covField X₂ Z q := by
    funext q
    exact D.add_direction q (X₁ q) (X₂ q) Z
  -- the bracket with the sum field on the left
  have hbr : lieDerivativeVectorField I (fun q => X₁ q + X₂ q) Y p
      = lieDerivativeVectorField I X₁ Y p + lieDerivativeVectorField I X₂ Y p := by
    calc lieDerivativeVectorField I (fun q => X₁ q + X₂ q) Y p
        = VectorField.mlieBracket I (X₁ + X₂) Y p := rfl
      _ = VectorField.mlieBracket I X₁ Y p + VectorField.mlieBracket I X₂ Y p :=
          VectorField.mlieBracket_add_left hX₁' hX₂'
      _ = lieDerivativeVectorField I X₁ Y p
            + lieDerivativeVectorField I X₂ Y p := rfl
  have h₁ : IsSmoothVectorField (D.covField X₁ Z) := D.smooth_cov hX₁ hZ
  have h₂ : IsSmoothVectorField (D.covField X₂ Z) := D.smooth_cov hX₂ hZ
  rw [curvatureTensor_apply, curvatureTensor_apply, curvatureTensor_apply,
    hcf, hbr, D.add_field p (Y p) h₁ h₂, D.add_direction, D.add_direction]
  module

/-- `R(fX, Y)Z = f · R(X,Y)Z` for a smooth function `f` and smooth fields: the
Leibniz correction from `∇_Y ∇_{fX} Z` is cancelled by the `−(D_Y f)·X` term of
the bracket `[fX, Y]`. -/
theorem curvatureTensor_smul_first (D : AffineConnection I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hZ : IsSmoothVectorField Z) (p : M) :
    curvatureTensor D (fun q => f q • X q) Y Z p
      = f p • curvatureTensor D X Y Z p := by
  have hcovXZ : IsSmoothVectorField (D.covField X Z) := D.smooth_cov hX hZ
  have hf' : MDifferentiableAt I 𝓘(ℝ) f p := (hf p).mdifferentiableAt (by simp)
  have hX' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, X q⟩ : TangentBundle I M)) p :=
    (hX p).mdifferentiableAt (by decide)
  -- ∇ in the direction of fX
  have hcf : D.covField (fun q => f q • X q) Z
      = fun q => f q • D.covField X Z q := by
    funext q
    exact D.smul_direction q (f q) (X q) Z
  -- the bracket [fX, Y]
  have hbr : lieDerivativeVectorField I (fun q => f q • X q) Y p
      = -(directionalDerivative Y f p) • X p
        + f p • lieDerivativeVectorField I X Y p := by
    calc lieDerivativeVectorField I (fun q => f q • X q) Y p
        = VectorField.mlieBracket I (f • X) Y p := rfl
      _ = -(directionalDerivative Y f p) • X p
            + f p • lieDerivativeVectorField I X Y p := by
          rw [VectorField.mlieBracket_smul_left hf' hX']
          rfl
  -- expand each of the three terms
  have T1 : D.cov p ((fun q => f q • X q) p) (D.covField Y Z)
      = f p • D.cov p (X p) (D.covField Y Z) :=
    D.smul_direction p (f p) (X p) (D.covField Y Z)
  have T2 : D.cov p (Y p) (D.covField (fun q => f q • X q) Z)
      = directionalDerivative Y f p • D.covField X Z p
        + f p • D.cov p (Y p) (D.covField X Z) := by
    rw [hcf, D.leibniz p (Y p) hf hcovXZ]
    rfl
  have T3 : D.cov p (lieDerivativeVectorField I (fun q => f q • X q) Y p) Z
      = -(directionalDerivative Y f p) • D.cov p (X p) Z
        + f p • D.cov p (lieDerivativeVectorField I X Y p) Z := by
    rw [hbr, D.add_direction, D.smul_direction, D.smul_direction]
  rw [curvatureTensor_apply, curvatureTensor_apply, T1, T2, T3]
  simp only [AffineConnection.covField_apply]
  module

/-- `R(X, Y₁ + Y₂)Z = R(X,Y₁)Z + R(X,Y₂)Z`, via antisymmetry. -/
theorem curvatureTensor_add_middle (D : AffineConnection I M)
    {X Y₁ Y₂ Z : Π x : M, TangentSpace I x}
    (hY₁ : IsSmoothVectorField Y₁) (hY₂ : IsSmoothVectorField Y₂)
    (hZ : IsSmoothVectorField Z) (p : M) :
    curvatureTensor D X (fun q => Y₁ q + Y₂ q) Z p
      = curvatureTensor D X Y₁ Z p + curvatureTensor D X Y₂ Z p := by
  rw [curvatureTensor_antisymm_first, curvatureTensor_add_first D hY₁ hY₂ hZ,
    curvatureTensor_antisymm_first D X Y₁ Z, curvatureTensor_antisymm_first D X Y₂ Z]
  module

/-- `R(X, fY)Z = f · R(X,Y)Z`, via antisymmetry. -/
theorem curvatureTensor_smul_middle (D : AffineConnection I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {X Y Z : Π x : M, TangentSpace I x}
    (hY : IsSmoothVectorField Y) (hZ : IsSmoothVectorField Z) (p : M) :
    curvatureTensor D X (fun q => f q • Y q) Z p
      = f p • curvatureTensor D X Y Z p := by
  rw [curvatureTensor_antisymm_first, curvatureTensor_smul_first D hf hY hZ,
    curvatureTensor_antisymm_first D X Y Z]
  module

end Homogeneity

/-! ## Locality: `R(X,Y)Z|_p` depends only on germs at `p` -/

section Locality

variable [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]
  [LocallyCompactSpace M]

/-- The value `R(X,Y)Z|_p` only depends on the germ of `Z` at `p`. -/
theorem curvatureTensor_congr_field (D : AffineConnection I M)
    {X Y Z₁ Z₂ : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ₁ : IsSmoothVectorField Z₁) (hZ₂ : IsSmoothVectorField Z₂)
    {p : M} (h : Z₁ =ᶠ[𝓝 p] Z₂) :
    curvatureTensor D X Y Z₁ p = curvatureTensor D X Y Z₂ p := by
  obtain ⟨U, hU, hUopen, hpU⟩ := eventually_nhds_iff.mp h
  have hEq : Set.EqOn Z₁ Z₂ U := fun q hq => hU q hq
  have hcfY : Set.EqOn (D.covField Y Z₁) (D.covField Y Z₂) U := fun q hq =>
    connection_local_openSet D (Y q) hZ₁ hZ₂ hUopen hq hEq
  have hcfX : Set.EqOn (D.covField X Z₁) (D.covField X Z₂) U := fun q hq =>
    connection_local_openSet D (X q) hZ₁ hZ₂ hUopen hq hEq
  have hY₁ : IsSmoothVectorField (D.covField Y Z₁) := D.smooth_cov hY hZ₁
  have hY₂ : IsSmoothVectorField (D.covField Y Z₂) := D.smooth_cov hY hZ₂
  have hX₁ : IsSmoothVectorField (D.covField X Z₁) := D.smooth_cov hX hZ₁
  have hX₂ : IsSmoothVectorField (D.covField X Z₂) := D.smooth_cov hX hZ₂
  rw [curvatureTensor_apply, curvatureTensor_apply,
    connection_local_openSet D (X p) hY₁ hY₂ hUopen hpU hcfY,
    connection_local_openSet D (Y p) hX₁ hX₂ hUopen hpU hcfX,
    connection_local_openSet D (lieDerivativeVectorField I X Y p) hZ₁ hZ₂
      hUopen hpU hEq]

/-- The value `R(X,Y)Z|_p` only depends on the germ of `X` at `p`. -/
theorem curvatureTensor_congr_first (D : AffineConnection I M)
    {X₁ X₂ Y Z : Π x : M, TangentSpace I x}
    (hX₁ : IsSmoothVectorField X₁) (hX₂ : IsSmoothVectorField X₂)
    (hZ : IsSmoothVectorField Z)
    {p : M} (h : X₁ =ᶠ[𝓝 p] X₂) :
    curvatureTensor D X₁ Y Z p = curvatureTensor D X₂ Y Z p := by
  obtain ⟨U, hU, hUopen, hpU⟩ := eventually_nhds_iff.mp h
  have hcf : Set.EqOn (D.covField X₁ Z) (D.covField X₂ Z) U := fun q hq => by
    show D.cov q (X₁ q) Z = D.cov q (X₂ q) Z
    rw [hU q hq]
  have hbr : lieDerivativeVectorField I X₁ Y p
      = lieDerivativeVectorField I X₂ Y p :=
    Filter.EventuallyEq.mlieBracket_vectorField_eq h Filter.EventuallyEq.rfl
  have h₁ : IsSmoothVectorField (D.covField X₁ Z) := D.smooth_cov hX₁ hZ
  have h₂ : IsSmoothVectorField (D.covField X₂ Z) := D.smooth_cov hX₂ hZ
  rw [curvatureTensor_apply, curvatureTensor_apply, hU p hpU, hbr,
    connection_local_openSet D (Y p) h₁ h₂ hUopen hpU hcf]

/-- The value `R(X,Y)Z|_p` only depends on the germ of `Y` at `p`. -/
theorem curvatureTensor_congr_middle (D : AffineConnection I M)
    {X Y₁ Y₂ Z : Π x : M, TangentSpace I x}
    (hY₁ : IsSmoothVectorField Y₁) (hY₂ : IsSmoothVectorField Y₂)
    (hZ : IsSmoothVectorField Z)
    {p : M} (h : Y₁ =ᶠ[𝓝 p] Y₂) :
    curvatureTensor D X Y₁ Z p = curvatureTensor D X Y₂ Z p := by
  rw [curvatureTensor_antisymm_first,
    curvatureTensor_congr_first D hY₁ hY₂ hZ h,
    ← curvatureTensor_antisymm_first]

end Locality

end PetersenLib
