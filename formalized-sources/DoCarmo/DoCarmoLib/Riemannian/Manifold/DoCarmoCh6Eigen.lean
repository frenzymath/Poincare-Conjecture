import DoCarmoLib.Riemannian.Manifold.DoCarmoCh6Pointwise
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh6Gauss
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# do Carmo Chapter 6 §2 — eigen-theory of the shape operator

The eigen-theory of the self-adjoint shape operator `S_η : T_pM → T_pM` at a
point (do Carmo Ex. 2.4, Rem. 2.6, Def. 2.10 and Ex. 2.8):

* `shapeOperatorHom` — the pointwise shape operator bundled as a linear
  endomorphism of the subspace `T_pM ⊆ T_pM̄`, symmetric for the ambient
  metric (`shapeOperatorHom_isSymmetric`);
* `principalCurvatures` / `principalDirections` — the **eigenvalues** and an
  orthonormal **eigenbasis** of `S_η` (do Carmo Ex. 2.4: principal curvatures
  and principal directions), via mathlib's finite-dimensional spectral
  theorem, with the instance-free forms `principalDirection`,
  `shapeOperatorAt_principalDirection`, `metricInner_principalDirection` and
  `secondFundScalarAt_principalDirection`;
* `gaussKroneckerCurvature` (`det S_η`) and `meanCurvature` (`(1/n) tr S_η`)
  with their eigenvalue formulas (do Carmo Ex. 2.4);
* `hypersurface_gauss` — do Carmo Rem. 2.6: in the codimension-one, unit-normal
  situation, `K(eᵢ, eⱼ) − K̄(eᵢ, eⱼ) = λᵢ λⱼ` on principal directions;
* `IsGeodesicAt` / `IsTotallyGeodesic` (do Carmo Ex. 2.8) with the
  characterization `isGeodesicAt_iff_secondFundFormAt_eq_zero`;
* `meanCurvatureVector` — the **mean curvature vector** `H ∈ (T_pM)^⊥`
  characterized by `⟨H, η⟩ = (1/n) tr S_η` (the frame-independence content of
  do Carmo's Def. 2.10), and **minimal immersions** `IsMinimal` with
  `isMinimal_iff_meanCurvatureVector_eq_zero`.

The fibrewise inner-product structure of mathlib (`OrthonormalBasis`, the
spectral theorem) is activated locally by pinning the two `g`-induced
instances `g.fiberNormedAddCommGroup p` and `g.fiberInnerProductSpace p` with
`letI`, under which `inner ℝ v w` is *definitionally* `g.metricInner p v w`;
all instance-free statements are phrased against `g.metricInner`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 6 §2, Ex. 2.4, Rem. 2.6,
Ex. 2.8 and Def. 2.10.
-/

open scoped ContDiff Manifold Topology Bundle InnerProductSpace

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Additivity of the metric in the first slot extended to finite
sums: `⟨Σᵢ vᵢ, w⟩ = Σᵢ ⟨vᵢ, w⟩`. -/
theorem RiemannianMetric.metricInner_sum_left (g : RiemannianMetric I M)
    (p : M) {ι : Type*} (s : Finset ι) (v : ι → TangentSpace I p)
    (w : TangentSpace I p) :
    g.metricInner p (∑ i ∈ s, v i) w = ∑ i ∈ s, g.metricInner p (v i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, g.metricInner_add_left, ih]

/-! ### The `g`-induced inner-product structure on a fibre

Mathlib's `OrthonormalBasis` and the finite-dimensional spectral theorem live
over `[NormedAddCommGroup V] [InnerProductSpace ℝ V]`. On the tangent fibre
`T_pM̄` these structures are induced by the metric `g` through mathlib's
`Bundle.RiemannianBundle` core; we *name* the two instances so that every
declaration of this file can pin them deterministically with `letI` (the
ambient `NormedAddCommGroup E` on `TangentSpace I p ≝ E` would otherwise
compete during synthesis, and it carries the wrong — non-`g` — norm). Under
these instances `inner ℝ v w` is definitionally `g.metricInner p v w`. -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Eng.** The `g`-induced `NormedAddCommGroup` on the fibre `T_pM̄` — the
norm of the inner product `g_p`, with the fibre's canonical topology (mathlib's
`Bundle.RiemannianBundle` routing, instance-named). -/
@[reducible] noncomputable def RiemannianMetric.fiberNormedAddCommGroup
    (g : RiemannianMetric I M) (p : M) :
    NormedAddCommGroup (TangentSpace I p) :=
  (g.toRiemannianMetric.toCore p).toNormedAddCommGroupOfTopology
    (g.toRiemannianMetric.continuousAt p) (g.toRiemannianMetric.isVonNBounded p)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Eng.** The `g`-induced `InnerProductSpace ℝ` on the fibre `T_pM̄`, over
`g.fiberNormedAddCommGroup p`; its `inner ℝ v w` is definitionally
`g.metricInner p v w`. -/
@[reducible] noncomputable def RiemannianMetric.fiberInnerProductSpace
    (g : RiemannianMetric I M) (p : M) :
    letI : NormedAddCommGroup (TangentSpace I p) := g.fiberNormedAddCommGroup p
    InnerProductSpace ℝ (TangentSpace I p) :=
  InnerProductSpace.ofCoreOfTopology (g.toRiemannianMetric.toCore p)
    (g.toRiemannianMetric.continuousAt p) (g.toRiemannianMetric.isVonNBounded p)

namespace DCImmersedPatch

variable {g : RiemannianMetric I M} (D : DCImmersedPatch I M g)
variable (nabla : AffineConnection I M)

/-! ### Linearity of the pointwise shape operator in the direction slot -/

omit [CompleteSpace E] in
/-- **Math.** Additivity of `S_η` in the direction: `S_η(x₁ + x₂) = S_η(x₁) +
S_η(x₂)` (do Carmo Def. 2.2: `S_η` is linear). -/
theorem shapeOperatorAt_add (p : M) (η x₁ x₂ : TangentSpace I p) :
    D.shapeOperatorAt nabla p η (x₁ + x₂)
      = D.shapeOperatorAt nabla p η x₁ + D.shapeOperatorAt nabla p η x₂ := by
  have hcongr : D.shapeOperatorAt nabla p η (x₁ + x₂)
      = D.shapeOperator nabla (D.normalExtension p η)
          (vectorFieldExtension p x₁ + vectorFieldExtension p x₂) p :=
    D.shapeOperator_congr_apply nabla (D.normalExtension p η) (by simp)
  rw [hcongr]
  have h : D.shapeOperator nabla (D.normalExtension p η)
        (vectorFieldExtension p x₁ + vectorFieldExtension p x₂)
      = D.shapeOperator nabla (D.normalExtension p η) (vectorFieldExtension p x₁)
        + D.shapeOperator nabla (D.normalExtension p η)
            (vectorFieldExtension p x₂) := by
    simp only [shapeOperator, nabla.add_left, D.tangentProj_add]
    ext q
    simp only [SmoothVectorField.neg_apply, SmoothVectorField.add_apply]
    module
  have h' := congrArg (fun F : SmoothVectorField I M => F p) h
  simp only [SmoothVectorField.add_apply] at h'
  exact h'

omit [CompleteSpace E] in
/-- **Math.** Homogeneity of `S_η` in the direction: `S_η(c x) = c S_η(x)`. -/
theorem shapeOperatorAt_smul (p : M) (η : TangentSpace I p) (c : ℝ)
    (x : TangentSpace I p) :
    D.shapeOperatorAt nabla p η (c • x) = c • D.shapeOperatorAt nabla p η x := by
  have hcongr : D.shapeOperatorAt nabla p η (c • x)
      = D.shapeOperator nabla (D.normalExtension p η)
          (SmoothVectorField.smul (fun _ => c) contMDiff_const
            (vectorFieldExtension p x)) p :=
    D.shapeOperator_congr_apply nabla (D.normalExtension p η) (by simp)
  rw [hcongr]
  have h : D.shapeOperator nabla (D.normalExtension p η)
        (SmoothVectorField.smul (fun _ => c) contMDiff_const
          (vectorFieldExtension p x))
      = SmoothVectorField.smul (fun _ => c) contMDiff_const
          (D.shapeOperator nabla (D.normalExtension p η)
            (vectorFieldExtension p x)) := by
    simp only [shapeOperator, nabla.smul_left, D.tangentProj_smul]
    ext q
    simp only [SmoothVectorField.neg_apply, SmoothVectorField.smul_apply]
    module
  have h' := congrArg (fun F : SmoothVectorField I M => F p) h
  simp only [SmoothVectorField.smul_apply] at h'
  exact h'

/-! ### The bundled shape operator on the tangent subspace (do Carmo Def. 2.2) -/

/-- **Math.** do Carmo Ch. 6, Def. 2.2 / Ex. 2.4: the shape operator at `p`
along `η` bundled as a **linear endomorphism of the subspace** `T_pM ⊆ T_pM̄`,
`S_η : T_pM →ₗ T_pM`. -/
noncomputable def shapeOperatorHom (p : M) (η : TangentSpace I p) :
    ↥(D.tang p) →ₗ[ℝ] ↥(D.tang p) where
  toFun x := ⟨D.shapeOperatorAt nabla p η ↑x, D.shapeOperatorAt_mem nabla p η ↑x⟩
  map_add' x y := Subtype.ext (by
    simp only [Submodule.coe_add]
    exact D.shapeOperatorAt_add nabla p η ↑x ↑y)
  map_smul' c x := Subtype.ext (by
    simp only [Submodule.coe_smul, RingHom.id_apply]
    exact D.shapeOperatorAt_smul nabla p η c ↑x)

omit [CompleteSpace E] in
@[simp] theorem coe_shapeOperatorHom_apply (p : M) (η : TangentSpace I p)
    (x : ↥(D.tang p)) :
    (D.shapeOperatorHom nabla p η x : TangentSpace I p)
      = D.shapeOperatorAt nabla p η ↑x := rfl

/-- **Math.** do Carmo Ch. 6, Def. 2.2: the bundled shape operator is
**symmetric** for the inner product induced by `g` on `T_pM` — the
`LinearMap.IsSymmetric` packaging of `inner_shapeOperatorAt_symm`. -/
theorem shapeOperatorHom_isSymmetric (hLC : nabla.IsLeviCivita g) (p : M)
    {η : TangentSpace I p} (hη : η ∈ D.normalSpace p) :
    letI : NormedAddCommGroup (TangentSpace I p) := g.fiberNormedAddCommGroup p
    letI : InnerProductSpace ℝ (TangentSpace I p) := g.fiberInnerProductSpace p
    LinearMap.IsSymmetric (D.shapeOperatorHom nabla p η) := by
  intro x y
  exact D.inner_shapeOperatorAt_symm nabla hLC hη x.2 y.2

/-! ### Principal curvatures and principal directions (do Carmo Ex. 2.4) -/

/-- **Math.** do Carmo Ch. 6, Ex. 2.4: the **principal curvatures** of the
immersion at `p` along the normal vector `η` — the eigenvalues `λ₁, …, λ_n` of
the self-adjoint shape operator `S_η : T_pM → T_pM`, via the finite-dimensional
spectral theorem. -/
noncomputable def principalCurvatures (hLC : nabla.IsLeviCivita g) (p : M)
    {η : TangentSpace I p} (hη : η ∈ D.normalSpace p) : Fin D.dim → ℝ :=
  letI : NormedAddCommGroup (TangentSpace I p) := g.fiberNormedAddCommGroup p
  letI : InnerProductSpace ℝ (TangentSpace I p) := g.fiberInnerProductSpace p
  LinearMap.IsSymmetric.eigenvalues
    (D.shapeOperatorHom_isSymmetric nabla hLC p hη) (D.finrank_tang p)

/-- **Math.** do Carmo Ch. 6, Ex. 2.4: an orthonormal basis `e₁, …, e_n` of
`T_pM` of **principal directions** — eigenvectors of the shape operator
`S_η`. -/
noncomputable def principalDirections (hLC : nabla.IsLeviCivita g) (p : M)
    {η : TangentSpace I p} (hη : η ∈ D.normalSpace p) :
    letI : NormedAddCommGroup (TangentSpace I p) := g.fiberNormedAddCommGroup p
    letI : InnerProductSpace ℝ (TangentSpace I p) := g.fiberInnerProductSpace p
    OrthonormalBasis (Fin D.dim) ℝ ↥(D.tang p) :=
  letI : NormedAddCommGroup (TangentSpace I p) := g.fiberNormedAddCommGroup p
  letI : InnerProductSpace ℝ (TangentSpace I p) := g.fiberInnerProductSpace p
  LinearMap.IsSymmetric.eigenvectorBasis
    (D.shapeOperatorHom_isSymmetric nabla hLC p hη) (D.finrank_tang p)

/-- **Math.** The `i`-th principal direction as a vector of the ambient
tangent space `T_pM̄` (the instance-free form of `principalDirections`). -/
noncomputable def principalDirection (hLC : nabla.IsLeviCivita g) (p : M)
    {η : TangentSpace I p} (hη : η ∈ D.normalSpace p) (i : Fin D.dim) :
    TangentSpace I p :=
  letI : NormedAddCommGroup (TangentSpace I p) := g.fiberNormedAddCommGroup p
  letI : InnerProductSpace ℝ (TangentSpace I p) := g.fiberInnerProductSpace p
  ↑(D.principalDirections nabla hLC p hη i)

/-- **Math.** Principal directions are tangent: `eᵢ ∈ T_pM`. -/
theorem principalDirection_mem (hLC : nabla.IsLeviCivita g) (p : M)
    {η : TangentSpace I p} (hη : η ∈ D.normalSpace p) (i : Fin D.dim) :
    D.principalDirection nabla hLC p hη i ∈ D.tang p := by
  letI : NormedAddCommGroup (TangentSpace I p) := g.fiberNormedAddCommGroup p
  letI : InnerProductSpace ℝ (TangentSpace I p) := g.fiberInnerProductSpace p
  exact (D.principalDirections nabla hLC p hη i).2

/-- **Math.** do Carmo Ch. 6, Ex. 2.4: the principal directions form an
**orthonormal** family in `T_pM`: `⟨eᵢ, eⱼ⟩ = δᵢⱼ`. -/
theorem metricInner_principalDirection (hLC : nabla.IsLeviCivita g) (p : M)
    {η : TangentSpace I p} (hη : η ∈ D.normalSpace p) (i j : Fin D.dim) :
    g.metricInner p (D.principalDirection nabla hLC p hη i)
        (D.principalDirection nabla hLC p hη j)
      = if i = j then 1 else 0 := by
  classical
  letI : NormedAddCommGroup (TangentSpace I p) := g.fiberNormedAddCommGroup p
  letI : InnerProductSpace ℝ (TangentSpace I p) := g.fiberInnerProductSpace p
  have h := (D.principalDirections nabla hLC p hη).orthonormal
  rw [orthonormal_iff_ite] at h
  exact h i j

/-- **Math.** do Carmo Ch. 6, Ex. 2.4: the defining eigen-relation of the
principal directions, `S_η(eᵢ) = λᵢ eᵢ`. -/
theorem shapeOperatorAt_principalDirection (hLC : nabla.IsLeviCivita g) (p : M)
    {η : TangentSpace I p} (hη : η ∈ D.normalSpace p) (i : Fin D.dim) :
    D.shapeOperatorAt nabla p η (D.principalDirection nabla hLC p hη i)
      = D.principalCurvatures nabla hLC p hη i
        • D.principalDirection nabla hLC p hη i := by
  letI : NormedAddCommGroup (TangentSpace I p) := g.fiberNormedAddCommGroup p
  letI : InnerProductSpace ℝ (TangentSpace I p) := g.fiberInnerProductSpace p
  have h := LinearMap.IsSymmetric.apply_eigenvectorBasis
    (D.shapeOperatorHom_isSymmetric nabla hLC p hη) (D.finrank_tang p) i
  exact congrArg (Subtype.val) h

/-- **Math.** The bundled eigen-relation `S_η(eᵢ) = λᵢ eᵢ` on the subspace
(`apply_eigenvectorBasis` for the shape operator). -/
theorem shapeOperatorHom_principalDirections (hLC : nabla.IsLeviCivita g)
    (p : M) {η : TangentSpace I p} (hη : η ∈ D.normalSpace p) (i : Fin D.dim) :
    letI : NormedAddCommGroup (TangentSpace I p) := g.fiberNormedAddCommGroup p
    letI : InnerProductSpace ℝ (TangentSpace I p) := g.fiberInnerProductSpace p
    D.shapeOperatorHom nabla p η (D.principalDirections nabla hLC p hη i)
      = D.principalCurvatures nabla hLC p hη i
        • D.principalDirections nabla hLC p hη i := by
  letI : NormedAddCommGroup (TangentSpace I p) := g.fiberNormedAddCommGroup p
  letI : InnerProductSpace ℝ (TangentSpace I p) := g.fiberInnerProductSpace p
  exact LinearMap.IsSymmetric.apply_eigenvectorBasis
    (D.shapeOperatorHom_isSymmetric nabla hLC p hη) (D.finrank_tang p) i

/-- **Math.** do Carmo Ch. 6, Ex. 2.4: the scalar second fundamental form is
**diagonalized** by the principal directions, `H_η(eᵢ, eⱼ) = λᵢ δᵢⱼ`. -/
theorem secondFundScalarAt_principalDirection (hLC : nabla.IsLeviCivita g)
    (p : M) {η : TangentSpace I p} (hη : η ∈ D.normalSpace p)
    (i j : Fin D.dim) :
    D.secondFundScalarAt nabla p η (D.principalDirection nabla hLC p hη i)
        (D.principalDirection nabla hLC p hη j)
      = if i = j then D.principalCurvatures nabla hLC p hη i else 0 := by
  classical
  rw [← D.inner_shapeOperatorAt nabla hLC.2 hη
      (D.principalDirection_mem nabla hLC p hη j)
      (D.principalDirection nabla hLC p hη i),
    D.shapeOperatorAt_principalDirection nabla hLC p hη i,
    g.metricInner_smul_left, D.metricInner_principalDirection nabla hLC p hη i j]
  by_cases h : i = j
  · simp [h]
  · simp [h]

/-! ### Gauss–Kronecker and mean curvature (do Carmo Ex. 2.4) -/

/-- **Math.** do Carmo Ch. 6, Ex. 2.4: the **Gauss–Kronecker curvature** of the
immersion at `p` along `η` — the determinant of the shape operator `S_η`. -/
noncomputable def gaussKroneckerCurvature (p : M) (η : TangentSpace I p) : ℝ :=
  LinearMap.det (D.shapeOperatorHom nabla p η)

/-- **Math.** do Carmo Ch. 6, Ex. 2.4 / Def. 2.10: the **mean curvature** of
the immersion at `p` along `η`, `(1/n) tr S_η`. -/
noncomputable def meanCurvature (p : M) (η : TangentSpace I p) : ℝ :=
  (D.dim : ℝ)⁻¹ * LinearMap.trace ℝ ↥(D.tang p) (D.shapeOperatorHom nabla p η)

/-- **Math.** The trace of the shape operator is the sum of the principal
curvatures, `tr S_η = Σᵢ λᵢ`. -/
theorem trace_shapeOperatorHom (hLC : nabla.IsLeviCivita g) (p : M)
    {η : TangentSpace I p} (hη : η ∈ D.normalSpace p) :
    LinearMap.trace ℝ ↥(D.tang p) (D.shapeOperatorHom nabla p η)
      = ∑ i, D.principalCurvatures nabla hLC p hη i := by
  letI : NormedAddCommGroup (TangentSpace I p) := g.fiberNormedAddCommGroup p
  letI : InnerProductSpace ℝ (TangentSpace I p) := g.fiberInnerProductSpace p
  exact LinearMap.IsSymmetric.trace_eq_sum_eigenvalues (D.finrank_tang p)
    (D.shapeOperatorHom_isSymmetric nabla hLC p hη)

/-- **Math.** do Carmo Ch. 6, Ex. 2.4: the mean curvature is the average of the
principal curvatures, `H_η = (1/n) Σᵢ λᵢ`. -/
theorem meanCurvature_eq_sum (hLC : nabla.IsLeviCivita g) (p : M)
    {η : TangentSpace I p} (hη : η ∈ D.normalSpace p) :
    D.meanCurvature nabla p η
      = (D.dim : ℝ)⁻¹ * ∑ i, D.principalCurvatures nabla hLC p hη i := by
  rw [meanCurvature, D.trace_shapeOperatorHom nabla hLC p hη]

/-- **Math.** do Carmo Ch. 6, Ex. 2.4: the Gauss–Kronecker curvature is the
product of the principal curvatures, `det S_η = Πᵢ λᵢ`. -/
theorem gaussKroneckerCurvature_eq_prod (hLC : nabla.IsLeviCivita g) (p : M)
    {η : TangentSpace I p} (hη : η ∈ D.normalSpace p) :
    D.gaussKroneckerCurvature nabla p η
      = ∏ i, D.principalCurvatures nabla hLC p hη i := by
  letI : NormedAddCommGroup (TangentSpace I p) := g.fiberNormedAddCommGroup p
  letI : InnerProductSpace ℝ (TangentSpace I p) := g.fiberInnerProductSpace p
  exact LinearMap.IsSymmetric.det_eq_prod_eigenvalues
    (D.shapeOperatorHom_isSymmetric nabla hLC p hη) (D.finrank_tang p)

/-! ### The hypersurface Gauss formula (do Carmo Rem. 2.6)

In the codimension-one situation — the normal space at `p` is spanned by a
unit normal `η` — the second fundamental form is scalar-valued,
`B(x, y) = H_η(x, y) η`, and Gauss' theorem on a pair of distinct principal
directions reads `K(eᵢ, eⱼ) − K̄(eᵢ, eⱼ) = λᵢ λⱼ`. -/

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 6, Rem. 2.6 (codimension one): with `η` a unit
normal spanning `(T_pM)^⊥`, the second fundamental form is determined by its
scalar form, `B(x, y) = H_η(x, y) η`. -/
theorem secondFundFormAt_eq_secondFundScalarAt_smul (p : M)
    {η : TangentSpace I p} (hunit : g.metricInner p η η = 1)
    (hcodim : ∀ w ∈ D.normalSpace p, ∃ c : ℝ, w = c • η)
    (x y : TangentSpace I p) :
    D.secondFundFormAt nabla p x y
      = D.secondFundScalarAt nabla p η x y • η := by
  obtain ⟨c, hc⟩ := hcodim _ (D.secondFundFormAt_mem nabla p x y)
  rw [secondFundScalarAt, hc, g.metricInner_smul_left, hunit, mul_one]

/-- **Math.** do Carmo Ch. 6, Rem. 2.6 — the **hypersurface Gauss formula**:
in codimension one with unit normal `η`, for distinct principal directions
`eᵢ ≠ eⱼ` (extended to tangent fields through `tangentExtension`),

`K(eᵢ, eⱼ) − K̄(eᵢ, eⱼ) = λᵢ λⱼ`,

the difference of the sectional curvatures of the immersed and ambient
manifolds in the plane spanned by `eᵢ, eⱼ` being the product of the two
principal curvatures. -/
theorem hypersurface_gauss (hLC : nabla.IsLeviCivita g) (p : M)
    {η : TangentSpace I p} (hη : η ∈ D.normalSpace p)
    (hunit : g.metricInner p η η = 1)
    (hcodim : ∀ w ∈ D.normalSpace p, ∃ c : ℝ, w = c • η)
    {i j : Fin D.dim} (hij : i ≠ j) :
    g.metricInner p (D.inducedCurvature nabla
        (D.tangentExtension p (D.principalDirection nabla hLC p hη i))
        (D.tangentExtension p (D.principalDirection nabla hLC p hη j))
        (D.tangentExtension p (D.principalDirection nabla hLC p hη i)) p)
        (D.tangentExtension p (D.principalDirection nabla hLC p hη j) p)
      - g.metricInner p (nabla.curvature
        (D.tangentExtension p (D.principalDirection nabla hLC p hη i))
        (D.tangentExtension p (D.principalDirection nabla hLC p hη j))
        (D.tangentExtension p (D.principalDirection nabla hLC p hη i)) p)
        (D.tangentExtension p (D.principalDirection nabla hLC p hη j) p)
      = D.principalCurvatures nabla hLC p hη i
        * D.principalCurvatures nabla hLC p hη j := by
  classical
  have hmi : D.principalDirection nabla hLC p hη i ∈ D.tang p :=
    D.principalDirection_mem nabla hLC p hη i
  have hmj : D.principalDirection nabla hLC p hη j ∈ D.tang p :=
    D.principalDirection_mem nabla hLC p hη j
  set X := D.tangentExtension p (D.principalDirection nabla hLC p hη i) with hX
  set Y := D.tangentExtension p (D.principalDirection nabla hLC p hη j) with hY
  have hXt : D.IsTangentField X :=
    D.isTangentField_tangentExtension p (D.principalDirection nabla hLC p hη i)
  have hYt : D.IsTangentField Y :=
    D.isTangentField_tangentExtension p (D.principalDirection nabla hLC p hη j)
  have hXp : X p = D.principalDirection nabla hLC p hη i :=
    D.tangentExtension_apply_self hmi
  have hYp : Y p = D.principalDirection nabla hLC p hη j :=
    D.tangentExtension_apply_self hmj
  -- Gauss' difference identity for the extensions
  have hgauss := D.inducedCurvature_inner_sub_curvature_inner nabla hLC hXt hYt p
  -- convert the `B`-of-fields values at `p` into pointwise `B` on `eᵢ, eⱼ`
  have hBXX : D.secondFundForm nabla X X p
      = D.secondFundFormAt nabla p (D.principalDirection nabla hLC p hη i)
          (D.principalDirection nabla hLC p hη i) := by
    rw [← D.secondFundFormAt_apply_apply nabla hXt X p, hXp]
  have hBYY : D.secondFundForm nabla Y Y p
      = D.secondFundFormAt nabla p (D.principalDirection nabla hLC p hη j)
          (D.principalDirection nabla hLC p hη j) := by
    rw [← D.secondFundFormAt_apply_apply nabla hYt Y p, hYp]
  have hBXY : D.secondFundForm nabla X Y p
      = D.secondFundFormAt nabla p (D.principalDirection nabla hLC p hη i)
          (D.principalDirection nabla hLC p hη j) := by
    rw [← D.secondFundFormAt_apply_apply nabla hYt X p, hXp, hYp]
  -- the diagonal and off-diagonal values of `H_η` on principal directions
  have hii : D.secondFundScalarAt nabla p η
        (D.principalDirection nabla hLC p hη i)
        (D.principalDirection nabla hLC p hη i)
      = D.principalCurvatures nabla hLC p hη i := by
    rw [D.secondFundScalarAt_principalDirection nabla hLC p hη i i, if_pos rfl]
  have hjj : D.secondFundScalarAt nabla p η
        (D.principalDirection nabla hLC p hη j)
        (D.principalDirection nabla hLC p hη j)
      = D.principalCurvatures nabla hLC p hη j := by
    rw [D.secondFundScalarAt_principalDirection nabla hLC p hη j j, if_pos rfl]
  have hij0 : D.secondFundScalarAt nabla p η
        (D.principalDirection nabla hLC p hη i)
        (D.principalDirection nabla hLC p hη j) = 0 := by
    rw [D.secondFundScalarAt_principalDirection nabla hLC p hη i j, if_neg hij]
  rw [hBXX, hBYY, hBXY,
    D.secondFundFormAt_eq_secondFundScalarAt_smul nabla p hunit hcodim
      (D.principalDirection nabla hLC p hη i)
      (D.principalDirection nabla hLC p hη i),
    D.secondFundFormAt_eq_secondFundScalarAt_smul nabla p hunit hcodim
      (D.principalDirection nabla hLC p hη j)
      (D.principalDirection nabla hLC p hη j),
    D.secondFundFormAt_eq_secondFundScalarAt_smul nabla p hunit hcodim
      (D.principalDirection nabla hLC p hη i)
      (D.principalDirection nabla hLC p hη j),
    hii, hjj, hij0] at hgauss
  rw [hgauss]
  simp only [zero_smul, g.metricInner_smul_left, g.metricInner_smul_right,
    g.metricInner_zero_left, hunit]
  ring

/-! ### Geodesic and totally geodesic immersions (do Carmo Ex. 2.8) -/

/-- **Math.** do Carmo Ch. 6, Ex. 2.8: the immersion is **geodesic at `p`**
when the second fundamental form `II_η` vanishes at `p` for every normal
`η`. -/
def IsGeodesicAt (p : M) : Prop :=
  ∀ η ∈ D.normalSpace p, ∀ x ∈ D.tang p, D.secondFundQuadAt nabla p η x = 0

/-- **Math.** do Carmo Ch. 6, Ex. 2.8: the immersion is **totally geodesic**
when it is geodesic at every point. -/
def IsTotallyGeodesic : Prop :=
  ∀ p, D.IsGeodesicAt nabla p

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Vectors of `(T_pM)^⊥` are separated by their inner products
against `(T_pM)^⊥` (the normal-space companion of
`eq_of_inner_eq_of_mem_tang`). -/
theorem eq_of_inner_eq_of_mem_normalSpace {p : M} {u v : TangentSpace I p}
    (hu : u ∈ D.normalSpace p) (hv : v ∈ D.normalSpace p)
    (h : ∀ w ∈ D.normalSpace p, g.metricInner p u w = g.metricInner p v w) :
    u = v := by
  by_contra hne
  have hpos := g.metricInner_self_pos p (u - v) (sub_ne_zero.mpr hne)
  have h0 : g.metricInner p (u - v) (u - v) = 0 := by
    rw [g.metricInner_sub_left, h (u - v) (sub_mem hu hv), sub_self]
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

/-- **Math.** do Carmo Ch. 6, Ex. 2.8: the immersion is geodesic at `p` iff
the (vector-valued) second fundamental form vanishes on `T_pM × T_pM` — by
polarization of `II_η` and separation on the normal space. In particular it is
totally geodesic iff `B ≡ 0`. -/
theorem isGeodesicAt_iff_secondFundFormAt_eq_zero (hLC : nabla.IsLeviCivita g)
    (p : M) :
    D.IsGeodesicAt nabla p ↔
      ∀ x ∈ D.tang p, ∀ y ∈ D.tang p, D.secondFundFormAt nabla p x y = 0 := by
  constructor
  · intro h x hx y hy
    refine D.eq_of_inner_eq_of_mem_normalSpace
      (D.secondFundFormAt_mem nabla p x y) (zero_mem _) fun w hw => ?_
    rw [g.metricInner_zero_left]
    -- polarize `II_w`: `2 H_w(x, y) = II_w(x + y) − II_w(x) − II_w(y)`
    have hxy := h w hw (x + y) (add_mem hx hy)
    have hx0 := h w hw x hx
    have hy0 := h w hw y hy
    simp only [secondFundQuadAt] at hxy hx0 hy0
    have hexp : D.secondFundScalarAt nabla p w (x + y) (x + y)
        = D.secondFundScalarAt nabla p w x x
          + D.secondFundScalarAt nabla p w x y
          + D.secondFundScalarAt nabla p w y x
          + D.secondFundScalarAt nabla p w y y := by
      simp only [secondFundScalarAt, D.secondFundFormAt_add_left,
        D.secondFundFormAt_add_right, g.metricInner_add_left]
      ring
    have hsymm := D.secondFundScalarAt_symm nabla hLC.1 w hx hy
    rw [hxy, hx0, hy0, hsymm] at hexp
    have hzero : D.secondFundScalarAt nabla p w x y = 0 := by linarith
    exact hzero
  · intro h η hη x hx
    simp only [secondFundQuadAt, secondFundScalarAt, h x hx x hx,
      g.metricInner_zero_left]

/-! ### Linearity of the shape operator in the normal vector -/

omit [CompleteSpace E] in
/-- **Math.** `S₀ = 0` on `T_pM̄` (the shape operator along the zero normal
vector vanishes). -/
theorem shapeOperatorAt_zero_normal (hcompat : nabla.IsMetricCompatible g)
    (p : M) (x : TangentSpace I p) :
    D.shapeOperatorAt nabla p 0 x = 0 := by
  refine D.eq_of_inner_eq_of_mem_tang (D.shapeOperatorAt_mem nabla p 0 x)
    (zero_mem _) fun w hw => ?_
  rw [D.inner_shapeOperatorAt nabla hcompat (zero_mem _) hw x,
    g.metricInner_zero_left, secondFundScalarAt, g.metricInner_zero_right]

omit [CompleteSpace E] in
/-- **Math.** Additivity of the shape operator in the normal vector:
`S_{η₁ + η₂} = S_{η₁} + S_{η₂}` for `η₁, η₂ ∈ (T_pM)^⊥` (implicit in do
Carmo's Def. 2.10: `η ↦ S_η` is linear on the normal space). -/
theorem shapeOperatorAt_add_normal (hcompat : nabla.IsMetricCompatible g)
    (p : M) {η₁ η₂ : TangentSpace I p} (hη₁ : η₁ ∈ D.normalSpace p)
    (hη₂ : η₂ ∈ D.normalSpace p) (x : TangentSpace I p) :
    D.shapeOperatorAt nabla p (η₁ + η₂) x
      = D.shapeOperatorAt nabla p η₁ x + D.shapeOperatorAt nabla p η₂ x := by
  refine D.eq_of_inner_eq_of_mem_tang (D.shapeOperatorAt_mem nabla p _ x)
    (add_mem (D.shapeOperatorAt_mem nabla p η₁ x)
      (D.shapeOperatorAt_mem nabla p η₂ x)) fun w hw => ?_
  rw [D.inner_shapeOperatorAt nabla hcompat (add_mem hη₁ hη₂) hw x,
    g.metricInner_add_left,
    D.inner_shapeOperatorAt nabla hcompat hη₁ hw x,
    D.inner_shapeOperatorAt nabla hcompat hη₂ hw x]
  simp only [secondFundScalarAt, g.metricInner_add_right]

omit [CompleteSpace E] in
/-- **Math.** Homogeneity of the shape operator in the normal vector:
`S_{cη} = c S_η` for `η ∈ (T_pM)^⊥`. -/
theorem shapeOperatorAt_smul_normal (hcompat : nabla.IsMetricCompatible g)
    (p : M) (c : ℝ) {η : TangentSpace I p} (hη : η ∈ D.normalSpace p)
    (x : TangentSpace I p) :
    D.shapeOperatorAt nabla p (c • η) x
      = c • D.shapeOperatorAt nabla p η x := by
  refine D.eq_of_inner_eq_of_mem_tang (D.shapeOperatorAt_mem nabla p _ x)
    (Submodule.smul_mem _ _ (D.shapeOperatorAt_mem nabla p η x)) fun w hw => ?_
  rw [D.inner_shapeOperatorAt nabla hcompat (Submodule.smul_mem _ _ hη) hw x,
    g.metricInner_smul_left, D.inner_shapeOperatorAt nabla hcompat hη hw x]
  simp only [secondFundScalarAt, g.metricInner_smul_right]

omit [CompleteSpace E] in
/-- **Math.** The bundled form of `shapeOperatorAt_add_normal`. -/
theorem shapeOperatorHom_add_normal (hcompat : nabla.IsMetricCompatible g)
    (p : M) {η₁ η₂ : TangentSpace I p} (hη₁ : η₁ ∈ D.normalSpace p)
    (hη₂ : η₂ ∈ D.normalSpace p) :
    D.shapeOperatorHom nabla p (η₁ + η₂)
      = D.shapeOperatorHom nabla p η₁ + D.shapeOperatorHom nabla p η₂ := by
  ext x
  exact D.shapeOperatorAt_add_normal nabla hcompat p hη₁ hη₂ ↑x

omit [CompleteSpace E] in
/-- **Math.** The bundled form of `shapeOperatorAt_smul_normal`. -/
theorem shapeOperatorHom_smul_normal (hcompat : nabla.IsMetricCompatible g)
    (p : M) (c : ℝ) {η : TangentSpace I p} (hη : η ∈ D.normalSpace p) :
    D.shapeOperatorHom nabla p (c • η) = c • D.shapeOperatorHom nabla p η := by
  ext x
  exact D.shapeOperatorAt_smul_normal nabla hcompat p c hη ↑x

omit [CompleteSpace E] in
/-- **Math.** `S` of a finite linear combination of normal vectors is the
corresponding combination of shape operators. -/
theorem shapeOperatorHom_sum_smul_normal (hcompat : nabla.IsMetricCompatible g)
    (p : M) {ι : Type*} (s : Finset ι) {v : ι → TangentSpace I p}
    (hv : ∀ i ∈ s, v i ∈ D.normalSpace p) (r : ι → ℝ) :
    D.shapeOperatorHom nabla p (∑ i ∈ s, r i • v i)
      = ∑ i ∈ s, r i • D.shapeOperatorHom nabla p (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    ext x
    exact D.shapeOperatorAt_zero_normal nabla hcompat p ↑x
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      D.shapeOperatorHom_add_normal nabla hcompat p
        (Submodule.smul_mem _ _ (hv a (Finset.mem_insert_self a s)))
        (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
          (hv i (Finset.mem_insert_of_mem hi))),
      D.shapeOperatorHom_smul_normal nabla hcompat p (r a)
        (hv a (Finset.mem_insert_self a s)),
      ih fun i hi => hv i (Finset.mem_insert_of_mem hi)]

/-! ### The mean curvature vector and minimal immersions (do Carmo Def. 2.10) -/

/-- **Math.** do Carmo Ch. 6, Def. 2.10: the immersion is **minimal** when
`tr S_η = 0` for every `p` and every normal `η` at `p`. -/
def IsMinimal : Prop :=
  ∀ (p : M), ∀ η ∈ D.normalSpace p,
    LinearMap.trace ℝ ↥(D.tang p) (D.shapeOperatorHom nabla p η) = 0

/-- **Math.** do Carmo Ch. 6, Def. 2.10: the **mean curvature vector**
`H = (1/n) Σᵢ (tr S_{Eᵢ}) Eᵢ ∈ (T_pM)^⊥` for an orthonormal basis `{Eᵢ}` of
the normal space — characterized frame-independently by
`inner_meanCurvatureVector`. -/
noncomputable def meanCurvatureVector (p : M) : TangentSpace I p :=
  letI : NormedAddCommGroup (TangentSpace I p) := g.fiberNormedAddCommGroup p
  letI : InnerProductSpace ℝ (TangentSpace I p) := g.fiberInnerProductSpace p
  ∑ i, ((D.dim : ℝ)⁻¹
      * LinearMap.trace ℝ ↥(D.tang p) (D.shapeOperatorHom nabla p
          ↑(stdOrthonormalBasis ℝ ↥(D.normalSpace p) i)))
    • (↑(stdOrthonormalBasis ℝ ↥(D.normalSpace p) i) : TangentSpace I p)

omit [CompleteSpace E] in
/-- **Math.** The mean curvature vector is normal: `H ∈ (T_pM)^⊥`. -/
theorem meanCurvatureVector_mem (p : M) :
    D.meanCurvatureVector nabla p ∈ D.normalSpace p := by
  letI : NormedAddCommGroup (TangentSpace I p) := g.fiberNormedAddCommGroup p
  letI : InnerProductSpace ℝ (TangentSpace I p) := g.fiberInnerProductSpace p
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (stdOrthonormalBasis ℝ ↥(D.normalSpace p) i).2

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 6, Def. 2.10 — the defining property of the mean
curvature vector: `⟨H, η⟩ = (1/n) tr S_η` for every normal `η`. Since the
right side does not mention the normal frame, this is the frame-independence
of `H`. -/
theorem inner_meanCurvatureVector (hcompat : nabla.IsMetricCompatible g)
    (p : M) {η : TangentSpace I p} (hη : η ∈ D.normalSpace p) :
    g.metricInner p (D.meanCurvatureVector nabla p) η
      = (D.dim : ℝ)⁻¹
        * LinearMap.trace ℝ ↥(D.tang p) (D.shapeOperatorHom nabla p η) := by
  letI : NormedAddCommGroup (TangentSpace I p) := g.fiberNormedAddCommGroup p
  letI : InnerProductSpace ℝ (TangentSpace I p) := g.fiberInnerProductSpace p
  set b := stdOrthonormalBasis ℝ ↥(D.normalSpace p) with hb
  -- the orthonormal expansion of `η` in the frame `b` of the normal space
  have hbridge : ∀ x y : ↥(D.normalSpace p),
      (inner ℝ x y : ℝ) = g.metricInner p ↑x ↑y := fun _ _ => rfl
  have hexp : η
      = ∑ i, g.metricInner p ↑(b i) η • (↑(b i) : TangentSpace I p) := by
    have h := congrArg (Subtype.val)
      (b.sum_repr' (⟨η, hη⟩ : ↥(D.normalSpace p)))
    simp only [Submodule.coe_sum, Submodule.coe_smul, hbridge] at h
    exact h.symm
  -- the trace of `S_η` through the expansion
  have htr : LinearMap.trace ℝ ↥(D.tang p) (D.shapeOperatorHom nabla p η)
      = ∑ i, g.metricInner p ↑(b i) η
          * LinearMap.trace ℝ ↥(D.tang p)
              (D.shapeOperatorHom nabla p ↑(b i)) := by
    conv_lhs => rw [hexp]
    rw [D.shapeOperatorHom_sum_smul_normal nabla hcompat p Finset.univ
      (fun i _ => (b i).2) (fun i => g.metricInner p ↑(b i) η), map_sum]
    simp only [map_smul, smul_eq_mul]
  have hunfold : D.meanCurvatureVector nabla p
      = ∑ i, ((D.dim : ℝ)⁻¹
          * LinearMap.trace ℝ ↥(D.tang p) (D.shapeOperatorHom nabla p ↑(b i)))
        • (↑(b i) : TangentSpace I p) := rfl
  rw [hunfold, g.metricInner_sum_left, htr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [g.metricInner_smul_left]
  ring

omit [CompleteSpace E] in
/-- **Math.** Uniqueness in do Carmo's Def. 2.10: any normal vector pairing as
`(1/n) tr S_η` against every normal `η` is the mean curvature vector. Together
with `meanCurvatureVector_mem` and `inner_meanCurvatureVector`, this shows the
mean curvature vector does not depend on the chosen orthonormal normal
frame. -/
theorem meanCurvatureVector_unique (hcompat : nabla.IsMetricCompatible g)
    (p : M) {v : TangentSpace I p} (hv : v ∈ D.normalSpace p)
    (h : ∀ η ∈ D.normalSpace p, g.metricInner p v η
      = (D.dim : ℝ)⁻¹
        * LinearMap.trace ℝ ↥(D.tang p) (D.shapeOperatorHom nabla p η)) :
    v = D.meanCurvatureVector nabla p :=
  D.eq_of_inner_eq_of_mem_normalSpace hv (D.meanCurvatureVector_mem nabla p)
    fun w hw => by
      rw [h w hw, D.inner_meanCurvatureVector nabla hcompat p hw]

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 6, Def. 2.10, packaged: there is a unique normal
vector `H ∈ (T_pM)^⊥` with `⟨H, η⟩ = (1/n) tr S_η` for all normal `η` — the
mean curvature vector of the immersion at `p`. -/
theorem existsUnique_meanCurvatureVector (hcompat : nabla.IsMetricCompatible g)
    (p : M) :
    ∃! Hvec : TangentSpace I p, Hvec ∈ D.normalSpace p ∧
      ∀ η ∈ D.normalSpace p, g.metricInner p Hvec η
        = (D.dim : ℝ)⁻¹
          * LinearMap.trace ℝ ↥(D.tang p) (D.shapeOperatorHom nabla p η) :=
  ⟨D.meanCurvatureVector nabla p,
    ⟨D.meanCurvatureVector_mem nabla p,
      fun _ hη => D.inner_meanCurvatureVector nabla hcompat p hη⟩,
    fun _ hv => D.meanCurvatureVector_unique nabla hcompat p hv.1 hv.2⟩

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 6, Def. 2.10: the immersion is minimal iff the mean
curvature vector vanishes at every point. -/
theorem isMinimal_iff_meanCurvatureVector_eq_zero
    (hcompat : nabla.IsMetricCompatible g) :
    D.IsMinimal nabla ↔ ∀ p, D.meanCurvatureVector nabla p = 0 := by
  constructor
  · intro h p
    refine D.eq_of_inner_eq_of_mem_normalSpace
      (D.meanCurvatureVector_mem nabla p) (zero_mem _) fun w hw => ?_
    rw [D.inner_meanCurvatureVector nabla hcompat p hw, h p w hw, mul_zero,
      g.metricInner_zero_left]
  · intro h p η hη
    have h0 := D.inner_meanCurvatureVector nabla hcompat p hη
    rw [h p, g.metricInner_zero_left] at h0
    rcases Nat.eq_zero_or_pos D.dim with hdim | hdim
    · -- `T_pM` has rank zero: every endomorphism has trace zero
      have hrank : Module.finrank ℝ ↥(D.tang p) = 0 := by
        rw [D.finrank_tang p, hdim]
      haveI : Subsingleton ↥(D.tang p) := Module.finrank_zero_iff.mp hrank
      rw [Subsingleton.elim (D.shapeOperatorHom nabla p η) 0, map_zero]
    · have hne : ((D.dim : ℝ))⁻¹ ≠ 0 := by
        simp only [ne_eq, inv_eq_zero, Nat.cast_eq_zero]
        omega
      exact (mul_eq_zero.mp h0.symm).resolve_left hne

end DCImmersedPatch

end Riemannian
