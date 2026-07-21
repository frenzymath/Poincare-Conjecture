import PetersenLib.Ch02.CovariantDerivative

/-!
# Petersen Ch. 3, §3.1.1 — The Curvature Tensor

The curvature tensor `R(X,Y)Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z`
(`curvatureTensor`), the Ricci-identity form
`R(X,Y)Z = ∇²_{X,Y}Z − ∇²_{Y,X}Z` through the second covariant derivative of a
vector field (`secondCovariantDerivativeField`,
`curvatureTensor_eq_ricci_identity`), antisymmetry in `(X,Y)`, additivity and
tensoriality (`C^∞(M)`-linearity) in `Z` (`curvatureTensor_tensorial`), and the
`(0,4)`-curvature tensor `R(X,Y,Z,W) = g(R(X,Y)Z, W)` (`curvatureTensorFour`).

## Design notes

* Vector fields are raw sections `Π x : M, TangentSpace I x` with explicit
  `IsSmoothVectorField` hypotheses, matching the Ch. 2 connection API.
* `curvatureTensor` is defined for any `AffineConnection`; Petersen's `R` is its
  specialization to the Riemannian (Levi-Civita) connection of `(M, g)`, for
  which the Ricci-identity form and the symmetries of §3.1 hold.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.1.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Further algebraic identities of the covariant derivative -/

namespace AffineConnection

variable (D : AffineConnection I M)

/-- `∇_0 X = 0`: the covariant derivative vanishes in the zero direction. -/
theorem cov_zero_direction (p : M) (X : Π x : M, TangentSpace I x) :
    D.cov p (0 : TangentSpace I p) X = 0 := by
  simpa using D.smul_direction p 0 0 X

/-- `∇_{−v} X = −∇_v X`. -/
theorem cov_neg_direction (p : M) (v : TangentSpace I p)
    (X : Π x : M, TangentSpace I x) :
    D.cov p (-v) X = -D.cov p v X := by
  simpa using D.smul_direction p (-1) v X

/-- `∇_{v−w} X = ∇_v X − ∇_w X`. -/
theorem cov_sub_direction (p : M) (v w : TangentSpace I p)
    (X : Π x : M, TangentSpace I x) :
    D.cov p (v - w) X = D.cov p v X - D.cov p w X := by
  rw [sub_eq_add_neg, D.add_direction, D.cov_neg_direction, ← sub_eq_add_neg]

/-- `∇_v 0 = 0`: the covariant derivative of the zero field vanishes. -/
theorem cov_zero_field (p : M) (v : TangentSpace I p) :
    D.cov p v (fun q : M => (0 : TangentSpace I q)) = 0 := by
  have h0 : IsSmoothVectorField (fun q : M => (0 : TangentSpace I q)) := by
    simpa using (0 : SmoothVectorField I M).smooth
  have h := D.add_field p v h0 h0
  have e : (fun q : M => (0 : TangentSpace I q) + 0)
      = fun q : M => (0 : TangentSpace I q) := by funext q; simp
  rw [e] at h
  have h2 : D.cov p v (fun q : M => (0 : TangentSpace I q)) + 0
      = D.cov p v (fun q : M => (0 : TangentSpace I q))
        + D.cov p v (fun q : M => (0 : TangentSpace I q)) := by
    rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- `∇_v (−X) = −∇_v X` for smooth `X`. -/
theorem cov_neg_field (p : M) (v : TangentSpace I p)
    {X : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X) :
    D.cov p v (fun q => -X q) = -D.cov p v X := by
  have hneg : IsSmoothVectorField (fun q : M => -X q) := by
    simpa using (-(⟨X, hX⟩ : SmoothVectorField I M)).smooth
  have h := D.add_field p v hX hneg
  have e : (fun q : M => X q + -X q) = fun q : M => (0 : TangentSpace I q) := by
    funext q; simp
  rw [e, D.cov_zero_field] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- `∇_v (X₁ − X₂) = ∇_v X₁ − ∇_v X₂` for smooth `X₁, X₂`. -/
theorem sub_field (p : M) (v : TangentSpace I p)
    {X₁ X₂ : Π x : M, TangentSpace I x}
    (h₁ : IsSmoothVectorField X₁) (h₂ : IsSmoothVectorField X₂) :
    D.cov p v (fun q => X₁ q - X₂ q) = D.cov p v X₁ - D.cov p v X₂ := by
  have hneg : IsSmoothVectorField (fun q : M => -X₂ q) := by
    simpa using (-(⟨X₂, h₂⟩ : SmoothVectorField I M)).smooth
  have e : (fun q : M => X₁ q - X₂ q) = fun q : M => X₁ q + -X₂ q := by
    funext q; rw [sub_eq_add_neg]
  rw [e, D.add_field p v h₁ hneg, D.cov_neg_field p v h₂, ← sub_eq_add_neg]

/-- The Leibniz rule at the level of fields:
`∇_Y (fZ) = (D_Y f) · Z + f · ∇_Y Z` as an identity of vector fields. -/
theorem covField_smul_field {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {Z : Π x : M, TangentSpace I x} (hZ : IsSmoothVectorField Z)
    (Y : Π x : M, TangentSpace I x) :
    D.covField Y (fun q => f q • Z q)
      = fun p => directionalDerivative Y f p • Z p + f p • D.covField Y Z p := by
  funext p
  exact D.leibniz p (Y p) hf hZ

end AffineConnection

/-! ## The curvature tensor -/

/-- **Math.** The **curvature tensor** (Petersen §3.1.1): for a connection `∇`
on `M`, the `(1,3)`-tensor defined on vector fields `X, Y, Z` by
`R(X,Y)Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z = [∇_X, ∇_Y]Z − ∇_{[X,Y]}Z`.
For the Riemannian connection this equals the Ricci-identity form
`∇²_{X,Y}Z − ∇²_{Y,X}Z` (`curvatureTensor_eq_ricci_identity`). Petersen's sign
convention. -/
def curvatureTensor (D : AffineConnection I M)
    (X Y Z : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  fun p => D.cov p (X p) (D.covField Y Z) - D.cov p (Y p) (D.covField X Z)
    - D.cov p (lieDerivativeVectorField I X Y p) Z

theorem curvatureTensor_apply (D : AffineConnection I M)
    (X Y Z : Π x : M, TangentSpace I x) (p : M) :
    curvatureTensor D X Y Z p
      = D.cov p (X p) (D.covField Y Z) - D.cov p (Y p) (D.covField X Z)
        - D.cov p (lieDerivativeVectorField I X Y p) Z := rfl

/-- Antisymmetry of the curvature tensor in its first two arguments,
`R(X,Y)Z = −R(Y,X)Z` — immediate from the definition and `[Y,X] = −[X,Y]`. -/
theorem curvatureTensor_antisymm_first (D : AffineConnection I M)
    (X Y Z : Π x : M, TangentSpace I x) (p : M) :
    curvatureTensor D X Y Z p = -curvatureTensor D Y X Z p := by
  rw [curvatureTensor_apply, curvatureTensor_apply]
  have hbr : D.cov p (lieDerivativeVectorField I Y X p) Z
      = -D.cov p (lieDerivativeVectorField I X Y p) Z := by
    rw [show lieDerivativeVectorField I Y X p = -(lieDerivativeVectorField I X Y p)
      from VectorField.mlieBracket_swap_apply, D.cov_neg_direction]
  rw [hbr]
  module

/-- `R(X,Y)Z` is a smooth vector field for smooth `X, Y, Z`. -/
theorem IsSmoothVectorField.curvatureTensor [I.Boundaryless] [CompleteSpace E]
    {D : AffineConnection I M}
    {X Y Z : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    (hY : IsSmoothVectorField Y) (hZ : IsSmoothVectorField Z) :
    IsSmoothVectorField (PetersenLib.curvatureTensor D X Y Z) := by
  have h₁ : IsSmoothVectorField (D.covField X (D.covField Y Z)) :=
    D.smooth_cov hX (D.smooth_cov hY hZ)
  have h₂ : IsSmoothVectorField (D.covField Y (D.covField X Z)) :=
    D.smooth_cov hY (D.smooth_cov hX hZ)
  have h₃ : IsSmoothVectorField
      (D.covField (PetersenLib.lieDerivativeVectorField I X Y) Z) :=
    D.smooth_cov (hX.lieDerivativeVectorField hY) hZ
  simpa using
    ((⟨_, h₁⟩ : SmoothVectorField I M) - ⟨_, h₂⟩ - ⟨_, h₃⟩).smooth

/-! ## The Ricci-identity form `R(X,Y)Z = ∇²_{X,Y}Z − ∇²_{Y,X}Z` -/

/-- The **second covariant derivative of a vector field** (Petersen §3.1.1):
`∇²_{X,Y}Z = ∇_X(∇_Y Z) − ∇_{∇_X Y}Z`, the `(1,2)`-tensor `(∇_X(∇Z))(Y)`. -/
def secondCovariantDerivativeField (D : AffineConnection I M)
    (X Y Z : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  fun p => D.cov p (X p) (D.covField Y Z) - D.cov p (D.covField X Y p) Z

theorem secondCovariantDerivativeField_apply (D : AffineConnection I M)
    (X Y Z : Π x : M, TangentSpace I x) (p : M) :
    secondCovariantDerivativeField D X Y Z p
      = D.cov p (X p) (D.covField Y Z) - D.cov p (D.covField X Y p) Z := rfl

/-- **Math.** The **Ricci identity** (Petersen §3.1.1): for the Riemannian
connection, `R(X,Y)Z = ∇²_{X,Y}Z − ∇²_{Y,X}Z` — the curvature tensor measures
the failure of second covariant derivatives to commute. The proof rewrites
`∇_{∇_X Y}Z − ∇_{∇_Y X}Z = ∇_{[X,Y]}Z` by torsion-freeness. -/
theorem curvatureTensor_eq_ricci_identity {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (Z : Π x : M, TangentSpace I x) (p : M) :
    curvatureTensor D.toAffineConnection X Y Z p
      = secondCovariantDerivativeField D.toAffineConnection X Y Z p
        - secondCovariantDerivativeField D.toAffineConnection Y X Z p := by
  rw [curvatureTensor_apply, secondCovariantDerivativeField_apply,
    secondCovariantDerivativeField_apply]
  have htf : D.cov p (D.toAffineConnection.covField X Y p) Z
        - D.cov p (D.toAffineConnection.covField Y X p) Z
      = D.cov p (lieDerivativeVectorField I X Y p) Z := by
    rw [← D.toAffineConnection.cov_sub_direction]
    congr 1
    simpa using D.torsion_free hX hY p
  linear_combination (norm := module) htf

/-! ## Additivity and tensoriality in `Z` -/

/-- `R(X,Y)(Z₁ + Z₂) = R(X,Y)Z₁ + R(X,Y)Z₂` for smooth fields. -/
theorem curvatureTensor_add_field (D : AffineConnection I M)
    {X Y Z₁ Z₂ : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ₁ : IsSmoothVectorField Z₁) (hZ₂ : IsSmoothVectorField Z₂) (p : M) :
    curvatureTensor D X Y (fun q => Z₁ q + Z₂ q) p
      = curvatureTensor D X Y Z₁ p + curvatureTensor D X Y Z₂ p := by
  have hcovY : D.covField Y (fun q => Z₁ q + Z₂ q)
      = fun q => D.covField Y Z₁ q + D.covField Y Z₂ q := by
    funext q
    exact D.add_field q (Y q) hZ₁ hZ₂
  have hcovX : D.covField X (fun q => Z₁ q + Z₂ q)
      = fun q => D.covField X Z₁ q + D.covField X Z₂ q := by
    funext q
    exact D.add_field q (X q) hZ₁ hZ₂
  have hY₁ : IsSmoothVectorField (D.covField Y Z₁) := D.smooth_cov hY hZ₁
  have hY₂ : IsSmoothVectorField (D.covField Y Z₂) := D.smooth_cov hY hZ₂
  have hX₁ : IsSmoothVectorField (D.covField X Z₁) := D.smooth_cov hX hZ₁
  have hX₂ : IsSmoothVectorField (D.covField X Z₂) := D.smooth_cov hX hZ₂
  rw [curvatureTensor_apply, curvatureTensor_apply, curvatureTensor_apply,
    hcovY, hcovX, D.add_field p (X p) hY₁ hY₂, D.add_field p (Y p) hX₁ hX₂,
    D.add_field p (lieDerivativeVectorField I X Y p) hZ₁ hZ₂]
  module

section Tensoriality

variable [I.Boundaryless] [CompleteSpace E]

/-- **Math.** **Tensoriality of the curvature tensor** (Petersen §3.1.1,
Lemma): `R(X,Y)Z` is `C^∞(M)`-linear in `Z`: for `f ∈ C^∞(M)`,
`R(X,Y)(fZ) = f · R(X,Y)Z`. The first-order Leibniz terms from the two double
covariant derivatives cancel each other, and the second-order terms cancel
against the `∇_{[X,Y]}` term through the commutator identity
`D_{[X,Y]} f = D_X D_Y f − D_Y D_X f` (symmetry of the Hessian of `f`). -/
theorem curvatureTensor_tensorial (D : AffineConnection I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (p : M) :
    curvatureTensor D X Y (fun q => f q • Z q) p
      = f p • curvatureTensor D X Y Z p := by
  -- smoothness bookkeeping
  have hdYf : ContMDiff I 𝓘(ℝ) ∞ (directionalDerivative Y f) :=
    hY.directionalDerivative_contMDiff hf
  have hdXf : ContMDiff I 𝓘(ℝ) ∞ (directionalDerivative X f) :=
    hX.directionalDerivative_contMDiff hf
  have hcovYZ : IsSmoothVectorField (D.covField Y Z) := D.smooth_cov hY hZ
  have hcovXZ : IsSmoothVectorField (D.covField X Z) := D.smooth_cov hX hZ
  have hsmulYZ : IsSmoothVectorField (fun q => directionalDerivative Y f q • Z q) := by
    simpa using (SmoothVectorField.smul _ hdYf ⟨Z, hZ⟩).smooth
  have hsmulXZ : IsSmoothVectorField (fun q => directionalDerivative X f q • Z q) := by
    simpa using (SmoothVectorField.smul _ hdXf ⟨Z, hZ⟩).smooth
  have hfcovY : IsSmoothVectorField (fun q => f q • D.covField Y Z q) := by
    simpa using (SmoothVectorField.smul _ hf ⟨_, hcovYZ⟩).smooth
  have hfcovX : IsSmoothVectorField (fun q => f q • D.covField X Z q) := by
    simpa using (SmoothVectorField.smul _ hf ⟨_, hcovXZ⟩).smooth
  -- ∇_X ∇_Y (fZ), expanded
  have T1 : D.cov p (X p) (D.covField Y (fun q => f q • Z q))
      = directionalDerivative X (directionalDerivative Y f) p • Z p
        + directionalDerivative Y f p • D.cov p (X p) Z
        + directionalDerivative X f p • D.covField Y Z p
        + f p • D.cov p (X p) (D.covField Y Z) := by
    rw [D.covField_smul_field hf hZ Y]
    have e : (fun p' => directionalDerivative Y f p' • Z p'
          + f p' • D.covField Y Z p')
        = fun q => (fun q' => directionalDerivative Y f q' • Z q') q
          + (fun q' => f q' • D.covField Y Z q') q := rfl
    rw [e, D.add_field p (X p) hsmulYZ hfcovY,
      D.leibniz p (X p) hdYf hZ, D.leibniz p (X p) hf hcovYZ,
      dirTangent_eq_directionalDerivative (directionalDerivative Y f) X p,
      dirTangent_eq_directionalDerivative f X p]
    module
  -- ∇_Y ∇_X (fZ), expanded
  have T2 : D.cov p (Y p) (D.covField X (fun q => f q • Z q))
      = directionalDerivative Y (directionalDerivative X f) p • Z p
        + directionalDerivative X f p • D.cov p (Y p) Z
        + directionalDerivative Y f p • D.covField X Z p
        + f p • D.cov p (Y p) (D.covField X Z) := by
    rw [D.covField_smul_field hf hZ X]
    have e : (fun p' => directionalDerivative X f p' • Z p'
          + f p' • D.covField X Z p')
        = fun q => (fun q' => directionalDerivative X f q' • Z q') q
          + (fun q' => f q' • D.covField X Z q') q := rfl
    rw [e, D.add_field p (Y p) hsmulXZ hfcovX,
      D.leibniz p (Y p) hdXf hZ, D.leibniz p (Y p) hf hcovXZ,
      dirTangent_eq_directionalDerivative (directionalDerivative X f) Y p,
      dirTangent_eq_directionalDerivative f Y p]
    module
  -- ∇_{[X,Y]} (fZ), expanded through the commutator identity
  have T3 : D.cov p (lieDerivativeVectorField I X Y p) (fun q => f q • Z q)
      = (directionalDerivative X (directionalDerivative Y f) p
          - directionalDerivative Y (directionalDerivative X f) p) • Z p
        + f p • D.cov p (lieDerivativeVectorField I X Y p) Z := by
    rw [D.leibniz p (lieDerivativeVectorField I X Y p) hf hZ]
    have hdir : dirTangent f (lieDerivativeVectorField I X Y p)
        = directionalDerivative (lieDerivativeVectorField I X Y) f p := rfl
    rw [hdir, lieDerivative_vectorField_eq_bracket hX hY hf p]
  rw [curvatureTensor_apply, curvatureTensor_apply, T1, T2, T3]
  simp only [AffineConnection.covField_apply]
  module

end Tensoriality

/-! ## The `(0,4)`-curvature tensor -/

/-- **Math.** The **`(0,4)`-curvature tensor** (Petersen §3.1.1): using the
metric, the curvature tensor is changed to a `(0,4)`-tensor by
`R(X,Y,Z,W) = g(R(X,Y)Z, W)`. -/
def curvatureTensorFour {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (X Y Z W : Π x : M, TangentSpace I x) :
    M → ℝ :=
  fun p => g.metricInner p (curvatureTensor D.toAffineConnection X Y Z p) (W p)

theorem curvatureTensorFour_apply {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (X Y Z W : Π x : M, TangentSpace I x)
    (p : M) :
    curvatureTensorFour D X Y Z W p
      = g.metricInner p (curvatureTensor D.toAffineConnection X Y Z p) (W p) :=
  rfl

end PetersenLib
