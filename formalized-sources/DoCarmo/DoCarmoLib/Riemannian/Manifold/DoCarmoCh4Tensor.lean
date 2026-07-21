import DoCarmoLib.Riemannian.Manifold.DoCarmoCh4

/-!
# do Carmo Chapter 4 §5 — tensors on Riemannian manifolds

Faithful Lean interface for do Carmo's Chapter 4 §5 (Tensors on Riemannian
manifolds). Building on the abstract affine connection `AffineConnection`
(Ch. 2), the metric `RiemannianMetric`, and the curvature 4-tensor
`AffineConnection.curvatureForm` (Ch. 4 §2), we formalise:

* the notion of a **covariant tensor** of order `r` as a `𝒟(M)`-multilinear
  map `𝒳(M)^r → 𝒟(M)` (`def:dc-ch4-5-1`), captured for `r = 2` and `r = 4` by
  the structures `IsCovariantTensor2` / `IsCovariantTensor3` /
  `IsCovariantTensor4` (additivity plus `𝒟(M)`-homogeneity in every slot);
* the **metric tensor** `G(X,Y) = ⟨X,Y⟩` and the fact that it is a tensor of
  order 2 (`ex:dc-ch4-5-3`);
* the fact that the **connection is not a tensor** (`ex:dc-ch4-5-4`): the
  order-3 form `∇(X,Y,Z) = ⟨∇_X Y, Z⟩` is `𝒟(M)`-linear in the direction slot
  `X` and the metric slot `Z`, but the Leibniz correction `(Xf)⟨Y,Z⟩` in the
  middle slot obstructs `𝒟(M)`-homogeneity, so it fails `IsCovariantTensor3`
  whenever that term is nonzero;
* the **curvature tensor** `R(X,Y,Z,T) = ⟨R(X,Y)Z, T⟩` as a tensor of order 4
  for a Levi-Civita connection (`ex:dc-ch4-5-2`);
* the **covariant differential** `∇T` of a tensor (`def:dc-ch4-5-7`), given for
  orders 1 and 2 by `covariantDifferential1` / `covariantDifferential2`;
* the vanishing of the covariant differential of the metric tensor,
  `∇G = 0` (`ex:dc-ch4-5-8`), a direct restatement of metric compatibility;
* the identification of the covariant derivative of the covector tensor
  `Y ↦ ⟨X,Y⟩` with the vector field `∇_Z X` (`ex:dc-ch4-5-9`).

Vector fields are the bundled `SmoothVectorField I M` (`= 𝒳(M)`); the smooth
scalars `𝒟(M)` are represented by `M → ℝ` together with a `ContMDiff` witness,
exactly as in the covariant-derivative interface of Chapters 2 and 4.

Reference: do Carmo, *Riemannian Geometry*, Ch. 4 §5.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The abstract notion of a covariant tensor (do Carmo Def. 5.1) -/

/-- **Math.** do Carmo Ch. 4, Def. 5.1 (order `2`): a **covariant tensor of order
2** is a map `T : 𝒳(M) × 𝒳(M) → 𝒟(M)` that is `𝒟(M)`-linear in each argument.
`𝒟(M)`-linearity is additivity together with homogeneity under a smooth scalar
factor `f ∈ 𝒟(M)`: `T(fX, Y) = f·T(X, Y)` and `T(X, fY) = f·T(X, Y)`. This
homogeneity is what makes `T(Y₁, Y₂)(p)` depend only on the values `Y₁(p), Y₂(p)`
— the tensoriality that distinguishes a tensor from a mere differential operator
(cf. `ex:dc-ch4-5-4`, the connection is *not* a tensor). -/
structure IsCovariantTensor2
    (T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ)) : Prop where
  add_left : ∀ (X₁ X₂ Y : SmoothVectorField I M) (p : M),
    T (X₁ + X₂) Y p = T X₁ Y p + T X₂ Y p
  add_right : ∀ (X Y₁ Y₂ : SmoothVectorField I M) (p : M),
    T X (Y₁ + Y₂) p = T X Y₁ p + T X Y₂ p
  smul_left : ∀ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y : SmoothVectorField I M) (p : M),
    T (SmoothVectorField.smul f hf X) Y p = f p * T X Y p
  smul_right : ∀ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y : SmoothVectorField I M) (p : M),
    T X (SmoothVectorField.smul f hf Y) p = f p * T X Y p

/-- **Math.** do Carmo Ch. 4, Def. 5.1 (order `4`): a **covariant tensor of order
4** is a map `T : 𝒳(M)^4 → 𝒟(M)` that is `𝒟(M)`-linear in each of its four
arguments. -/
structure IsCovariantTensor4
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ)) : Prop where
  add₁ : ∀ (X₁ X₂ Y Z W : SmoothVectorField I M) (p : M),
    T (X₁ + X₂) Y Z W p = T X₁ Y Z W p + T X₂ Y Z W p
  add₂ : ∀ (X Y₁ Y₂ Z W : SmoothVectorField I M) (p : M),
    T X (Y₁ + Y₂) Z W p = T X Y₁ Z W p + T X Y₂ Z W p
  add₃ : ∀ (X Y Z₁ Z₂ W : SmoothVectorField I M) (p : M),
    T X Y (Z₁ + Z₂) W p = T X Y Z₁ W p + T X Y Z₂ W p
  add₄ : ∀ (X Y Z W₁ W₂ : SmoothVectorField I M) (p : M),
    T X Y Z (W₁ + W₂) p = T X Y Z W₁ p + T X Y Z W₂ p
  smul₁ : ∀ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y Z W : SmoothVectorField I M) (p : M),
    T (SmoothVectorField.smul f hf X) Y Z W p = f p * T X Y Z W p
  smul₂ : ∀ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y Z W : SmoothVectorField I M) (p : M),
    T X (SmoothVectorField.smul f hf Y) Z W p = f p * T X Y Z W p
  smul₃ : ∀ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y Z W : SmoothVectorField I M) (p : M),
    T X Y (SmoothVectorField.smul f hf Z) W p = f p * T X Y Z W p
  smul₄ : ∀ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y Z W : SmoothVectorField I M) (p : M),
    T X Y Z (SmoothVectorField.smul f hf W) p = f p * T X Y Z W p

/-- **Math.** do Carmo Ch. 4, Def. 5.1 (order `3`): a **covariant tensor of order
3** is a map `T : 𝒳(M)^3 → 𝒟(M)` that is `𝒟(M)`-linear in each of its three
arguments. Used to state that the connection `∇(X, Y, Z) = ⟨∇_X Y, Z⟩` is *not* a
tensor (`ex:dc-ch4-5-4`): it is `𝒟(M)`-linear in the first and third slots but
fails homogeneity in the middle slot because of the Leibniz correction term. -/
structure IsCovariantTensor3
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      (M → ℝ)) : Prop where
  add₁ : ∀ (X₁ X₂ Y Z : SmoothVectorField I M) (p : M),
    T (X₁ + X₂) Y Z p = T X₁ Y Z p + T X₂ Y Z p
  add₂ : ∀ (X Y₁ Y₂ Z : SmoothVectorField I M) (p : M),
    T X (Y₁ + Y₂) Z p = T X Y₁ Z p + T X Y₂ Z p
  add₃ : ∀ (X Y Z₁ Z₂ : SmoothVectorField I M) (p : M),
    T X Y (Z₁ + Z₂) p = T X Y Z₁ p + T X Y Z₂ p
  smul₁ : ∀ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y Z : SmoothVectorField I M) (p : M),
    T (SmoothVectorField.smul f hf X) Y Z p = f p * T X Y Z p
  smul₂ : ∀ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y Z : SmoothVectorField I M) (p : M),
    T X (SmoothVectorField.smul f hf Y) Z p = f p * T X Y Z p
  smul₃ : ∀ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y Z : SmoothVectorField I M) (p : M),
    T X Y (SmoothVectorField.smul f hf Z) p = f p * T X Y Z p

/-! ### The metric tensor (do Carmo Ex. 5.3) -/

/-- **Math.** do Carmo Ch. 4, Ex. 5.3: the **metric tensor**
`G(X, Y) = ⟨X, Y⟩`, a covariant tensor of order 2 whose components in a
coordinate frame are the metric coefficients `g_{ij}`. -/
def metricTensor (g : RiemannianMetric I M) (X Y : SmoothVectorField I M) : M → ℝ :=
  fun p => g.metricInner p (X p) (Y p)

omit [CompleteSpace E] in
@[simp] theorem metricTensor_apply (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (p : M) :
    metricTensor g X Y p = g.metricInner p (X p) (Y p) := rfl

omit [CompleteSpace E] in
/-- **Math.** The metric tensor is symmetric, `G(X, Y) = G(Y, X)`. -/
theorem metricTensor_symm (g : RiemannianMetric I M) (X Y : SmoothVectorField I M) :
    metricTensor g X Y = metricTensor g Y X := by
  funext p; exact g.metricInner_comm p (X p) (Y p)

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 4, Ex. 5.3: the metric tensor `G` is a tensor of order
2. Bilinearity over `𝒟(M)` is inherited slotwise from the bilinearity of the
inner product `g_p`. -/
theorem metricTensor_isCovariantTensor2 (g : RiemannianMetric I M) :
    IsCovariantTensor2 (metricTensor (I := I) (M := M) g) where
  add_left X₁ X₂ Y p := by
    simp only [metricTensor, SmoothVectorField.add_apply,
      RiemannianMetric.metricInner_add_left]
  add_right X Y₁ Y₂ p := by
    simp only [metricTensor, SmoothVectorField.add_apply,
      RiemannianMetric.metricInner_add_right]
  smul_left f hf X Y p := by
    simp only [metricTensor, SmoothVectorField.smul_apply,
      RiemannianMetric.metricInner_smul_left]
  smul_right f hf X Y p := by
    simp only [metricTensor, SmoothVectorField.smul_apply,
      RiemannianMetric.metricInner_smul_right]

/-! ### The curvature tensor (do Carmo Ex. 5.2) -/

namespace AffineConnection

variable (nabla : AffineConnection I M)

section CurvatureTensor

variable [I.Boundaryless] (g : RiemannianMetric I M)

/-- **Math.** do Carmo Ch. 4, Ex. 5.2: for a Levi-Civita connection the curvature
4-tensor `R(X, Y, Z, W) = ⟨R(X,Y)Z, W⟩` (`AffineConnection.curvatureForm`) is a
tensor of order 4. Multilinearity in the first three slots is the `𝒟(M)`-linearity
of the curvature operator `R(X,Y)Z` (`prop:dc-ch4-2-2`: `curvature_add_*`,
`curvature_smul_*`); multilinearity in the last slot is the bilinearity of the
metric. Antisymmetries `prop:dc-ch4-2-5` are recorded separately in
`DoCarmoCh4.lean`. -/
theorem curvatureForm_isCovariantTensor4 :
    IsCovariantTensor4 (nabla.curvatureForm g) where
  add₁ X₁ X₂ Y Z W p := by
    simp only [curvatureForm, nabla.curvature_add_left X₁ X₂ Y Z,
      RiemannianMetric.metricInner_add_left]
  add₂ X Y₁ Y₂ Z W p := by
    simp only [curvatureForm, nabla.curvature_add_middle X Y₁ Y₂ Z,
      RiemannianMetric.metricInner_add_left]
  add₃ X Y Z₁ Z₂ W p := by
    simp only [curvatureForm, nabla.curvature_add_right X Y Z₁ Z₂,
      RiemannianMetric.metricInner_add_left]
  add₄ X Y Z W₁ W₂ p := by
    simp only [curvatureForm, SmoothVectorField.add_apply,
      RiemannianMetric.metricInner_add_right]
  smul₁ f hf X Y Z W p := by
    simp only [curvatureForm, nabla.curvature_smul_left hf X Y Z,
      RiemannianMetric.metricInner_smul_left]
  smul₂ f hf X Y Z W p := by
    simp only [curvatureForm, nabla.curvature_smul_middle hf X Y Z,
      RiemannianMetric.metricInner_smul_left]
  smul₃ f hf X Y Z W p := by
    simp only [curvatureForm, nabla.curvature_smul_right hf X Y Z,
      RiemannianMetric.metricInner_smul_left]
  smul₄ f hf X Y Z W p := by
    simp only [curvatureForm, SmoothVectorField.smul_apply,
      RiemannianMetric.metricInner_smul_right]

end CurvatureTensor

/-! ### The covariant differential of a tensor (do Carmo Def. 5.7) -/

/-- **Math.** do Carmo Ch. 4, Def. 5.7 (order `1`): the **covariant differential**
`∇T` of an order-1 covariant tensor `T : 𝒳(M) → 𝒟(M)` is the order-2 tensor
`∇T(Y, Z) = Z(T(Y)) − T(∇_Z Y)`. -/
def covariantDifferential1 (T : SmoothVectorField I M → (M → ℝ))
    (Y Z : SmoothVectorField I M) : M → ℝ :=
  fun p => Z.dir (T Y) p - T (nabla.cov Z Y) p

/-- **Math.** do Carmo Ch. 4, Def. 5.7 (order `2`): the **covariant differential**
`∇T` of an order-2 covariant tensor `T : 𝒳(M) × 𝒳(M) → 𝒟(M)` is the order-3
tensor `∇T(X, Y, Z) = Z(T(X, Y)) − T(∇_Z X, Y) − T(X, ∇_Z Y)`. For each `Z`, the
**covariant derivative** `∇_Z T(X, Y) = ∇T(X, Y, Z)`. -/
def covariantDifferential2
    (T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (X Y Z : SmoothVectorField I M) : M → ℝ :=
  fun p => Z.dir (T X Y) p - T (nabla.cov Z X) Y p - T X (nabla.cov Z Y) p

/-! ### `∇G = 0` (do Carmo Ex. 5.8) -/

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 4, Ex. 5.8: the **covariant differential of the metric
tensor is the zero tensor**, `∇G = 0`. Indeed
`∇G(X, Y, Z) = Z⟨X,Y⟩ − ⟨∇_Z X, Y⟩ − ⟨X, ∇_Z Y⟩`, which vanishes precisely
because `∇` is compatible with the metric (`IsMetricCompatible`, do Carmo eq. (4)):
`Z⟨X,Y⟩ = ⟨∇_Z X, Y⟩ + ⟨X, ∇_Z Y⟩`. -/
theorem covariantDifferential2_metricTensor_eq_zero (g : RiemannianMetric I M)
    (hcompat : nabla.IsMetricCompatible g)
    (X Y Z : SmoothVectorField I M) (p : M) :
    nabla.covariantDifferential2 (metricTensor g) X Y Z p = 0 := by
  have h : Z.dir (metricTensor g X Y) p
      = g.metricInner p ((nabla.cov Z X) p) (Y p)
        + g.metricInner p (X p) ((nabla.cov Z Y) p) := hcompat Z X Y p
  simp only [covariantDifferential2, metricTensor]
  linarith [h]

/-! ### `∇_Z X` as a tensor is the vector field `∇_Z X` (do Carmo Ex. 5.9) -/

/-- **Math.** do Carmo Ch. 4, Rem. 5.6 / Ex. 5.9: identify a vector field
`X ∈ 𝒳(M)` with the order-1 covector tensor `Y ↦ ⟨X, Y⟩`. -/
def covectorTensor (g : RiemannianMetric I M) (X : SmoothVectorField I M) :
    SmoothVectorField I M → (M → ℝ) :=
  fun Y p => g.metricInner p (X p) (Y p)

omit [CompleteSpace E] in
@[simp] theorem covectorTensor_apply (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (p : M) :
    covectorTensor g X Y p = g.metricInner p (X p) (Y p) := rfl

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 4, Ex. 5.9: the covariant derivative of the covector
tensor `Y ↦ ⟨X, Y⟩` associated with `X` is the covector tensor associated with the
vector field `∇_Z X`:
`∇(covectorTensor X)(Y, Z) = Z⟨X, Y⟩ − ⟨X, ∇_Z Y⟩ = ⟨∇_Z X, Y⟩`.
This shows the covariant derivative of tensors generalises the covariant
derivative of vector fields, and justifies the notation `∇_Z X`. -/
theorem covariantDifferential1_covectorTensor_eq (g : RiemannianMetric I M)
    (hcompat : nabla.IsMetricCompatible g)
    (X Y Z : SmoothVectorField I M) (p : M) :
    nabla.covariantDifferential1 (covectorTensor g X) Y Z p
      = g.metricInner p ((nabla.cov Z X) p) (Y p) := by
  have h : Z.dir (covectorTensor g X Y) p
      = g.metricInner p ((nabla.cov Z X) p) (Y p)
        + g.metricInner p (X p) ((nabla.cov Z Y) p) := hcompat Z X Y p
  simp only [covariantDifferential1, covectorTensor]
  linarith [h]

/-! ### The connection is not a tensor (do Carmo Ex. 5.4) -/

/-- **Math.** do Carmo Ch. 4, Ex. 5.4: the order-3 form associated with the
connection, `∇(X, Y, Z) = ⟨∇_X Y, Z⟩`. It is `𝒟(M)`-linear in the direction slot
`X` and in the metric slot `Z`, but *not* in the differentiated slot `Y` — see
`connectionForm_smul_middle`. -/
def connectionForm (g : RiemannianMetric I M) (X Y Z : SmoothVectorField I M) :
    M → ℝ :=
  fun p => g.metricInner p ((nabla.cov X Y) p) (Z p)

omit [CompleteSpace E] in
@[simp] theorem connectionForm_apply (g : RiemannianMetric I M)
    (X Y Z : SmoothVectorField I M) (p : M) :
    nabla.connectionForm g X Y Z p = g.metricInner p ((nabla.cov X Y) p) (Z p) :=
  rfl

omit [CompleteSpace E] in
/-- **Math.** `∇(·, Y, Z)` is `𝒟(M)`-homogeneous in the **direction** slot:
`∇(fX, Y, Z) = f · ∇(X, Y, Z)`, since the connection is `𝒟(M)`-linear in its
first argument. -/
theorem connectionForm_smul_left (g : RiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (X Y Z : SmoothVectorField I M) (p : M) :
    nabla.connectionForm g (SmoothVectorField.smul f hf X) Y Z p
      = f p * nabla.connectionForm g X Y Z p := by
  simp only [connectionForm, nabla.smul_left f hf X Y, SmoothVectorField.smul_apply,
    RiemannianMetric.metricInner_smul_left]

omit [CompleteSpace E] in
/-- **Math.** `∇(X, Y, ·)` is `𝒟(M)`-homogeneous in the **metric** slot:
`∇(X, Y, fZ) = f · ∇(X, Y, Z)`, by bilinearity of the inner product. -/
theorem connectionForm_smul_right (g : RiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (X Y Z : SmoothVectorField I M) (p : M) :
    nabla.connectionForm g X Y (SmoothVectorField.smul f hf Z) p
      = f p * nabla.connectionForm g X Y Z p := by
  simp only [connectionForm, SmoothVectorField.smul_apply,
    RiemannianMetric.metricInner_smul_right]

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 4, Ex. 5.4, the crux: in the **differentiated** slot
the connection obeys the Leibniz rule, not homogeneity:
`∇(X, fY, Z) = f · ∇(X, Y, Z) + (Xf) · ⟨Y, Z⟩`.
The extra term `(Xf)⟨Y, Z⟩` is exactly what an order-3 tensor would forbid. -/
theorem connectionForm_smul_middle (g : RiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (X Y Z : SmoothVectorField I M) (p : M) :
    nabla.connectionForm g X (SmoothVectorField.smul f hf Y) Z p
      = f p * nabla.connectionForm g X Y Z p
        + X.dir f p * g.metricInner p (Y p) (Z p) := by
  simp only [connectionForm, nabla.leibniz f hf X Y p,
    RiemannianMetric.metricInner_add_left, RiemannianMetric.metricInner_smul_left]

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 4, Ex. 5.4: the connection `∇(X, Y, Z) = ⟨∇_X Y, Z⟩`
is **not a tensor**. Formalised as an honest obstruction: whenever there is a
configuration `(X, Y, Z, f, p)` at which the Leibniz correction term
`(Xf)(p) · ⟨Y(p), Z(p)⟩` is nonzero, the connection form fails `𝒟(M)`-homogeneity
in its middle slot, hence is not an order-3 covariant tensor. (Some nondegeneracy
witness is unavoidable: on a `0`-dimensional manifold every `Xf` vanishes and the
connection *is* trivially a tensor.) -/
theorem connectionForm_not_isCovariantTensor (g : RiemannianMetric I M)
    (hwit : ∃ (X Y Z : SmoothVectorField I M) (f : M → ℝ)
      (_ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M),
      X.dir f p * g.metricInner p (Y p) (Z p) ≠ 0) :
    ¬ IsCovariantTensor3 (nabla.connectionForm g) := by
  rintro hT
  obtain ⟨X, Y, Z, f, hf, p, hne⟩ := hwit
  have h1 := hT.smul₂ f hf X Y Z p
  have h2 := nabla.connectionForm_smul_middle g hf X Y Z p
  rw [h1] at h2
  exact hne (by linarith [h2])

end AffineConnection

end Riemannian
