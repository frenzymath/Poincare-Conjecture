import DoCarmoLib.Riemannian.Manifold.DoCarmoCh6

/-!
# do Carmo Chapter 6 §3 — the fundamental equations of an isometric immersion

Continuation of `DoCarmoCh6`: for an immersed patch `D` in the ambient
Riemannian manifold `(M̄, g)` with Riemannian connection `∇̄`, we introduce the
remaining first-order invariants and prove the three fundamental equations of
the local theory of isometric immersions:

* the **shape operator** `S_η(X) = −(∇̄_X η)ᵀ` and the **normal connection**
  `∇^⊥_X η = (∇̄_X η)ᴺ`, giving the Weingarten decomposition
  `∇̄_X η = −S_η(X) + ∇^⊥_X η` (eq. (5));
* the Weingarten pairing `⟨S_η(X), Y⟩ = ⟨B(X, Y), η⟩` (the field-level content
  of do Carmo's Prop. 2.3 and Def. 2.2) and the self-adjointness of `S_η`;
* the **normal curvature** `R^⊥(X,Y)η = ∇^⊥_Y ∇^⊥_X η − ∇^⊥_X ∇^⊥_Y η +
  ∇^⊥_{[X,Y]} η` and the curvature `R` of the induced connection;
* the decomposition (6) of the ambient curvature `R̄(X,Y)Z` into tangential and
  normal parts, and its normal-argument analogue for `R̄(X,Y)η`;
* the **Gauss equation**, the **Ricci equation** (`prop:dc-ch6-3-1`) and the
  **Codazzi equation** (`prop:dc-ch6-3-4`), with the covariant derivative
  `(∇̄_X B)(Y, Z, η)` of the second fundamental form regarded as a scalar
  tensor (`rem:dc-ch6-3-3`).

All statements are field-level identities evaluated at a point; the tangency /
normality hypotheses carried by each result are exactly the ones its proof
uses, and for tangent fields `X, Y, Z, T` and normal fields `η, ζ` they read as
do Carmo's equations verbatim.

Reference: do Carmo, *Riemannian Geometry*, Ch. 6 §2–§3.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace DCImmersedPatch

variable {g : RiemannianMetric I M} (D : DCImmersedPatch I M g)
variable (nabla : AffineConnection I M)

/-! ### The shape operator and the normal connection (do Carmo Ch. 6 §3, eq. (5)) -/

/-- **Math.** do Carmo Ch. 6 §3: the **shape operator** (Weingarten operator)
`S_η(X) = −(∇̄_X η)ᵀ`, the negated tangential part of the ambient covariant
derivative of `η` in the direction `X`. For `η` normal and `X` tangent this is
do Carmo's `S_η` (cf. Prop. 2.3); the formula makes sense for arbitrary ambient
fields. -/
def shapeOperator (η X : SmoothVectorField I M) : SmoothVectorField I M :=
  -(D.tangentProj (nabla.cov X η))

/-- **Math.** do Carmo Ch. 6 §3, eq. (5): the **normal connection**
`∇^⊥_X η = (∇̄_X η)ᴺ`, the normal part of the ambient covariant derivative. -/
def normalCov (X η : SmoothVectorField I M) : SmoothVectorField I M :=
  D.normalProj (nabla.cov X η)

omit [CompleteSpace E] in
/-- **Math.** The **Weingarten decomposition** (do Carmo Ch. 6 §3, eq. (5)):
`∇̄_X η = −S_η(X) + ∇^⊥_X η`. -/
theorem cov_eq_neg_shapeOperator_add_normalCov (X η : SmoothVectorField I M) :
    nabla.cov X η = -(D.shapeOperator nabla η X) + D.normalCov nabla X η := by
  ext p
  simp only [SmoothVectorField.add_apply, SmoothVectorField.neg_apply,
    shapeOperator, normalCov, normalProj_apply]
  module

omit [CompleteSpace E] in
/-- **Math.** `S_η(X)(p) ∈ T_pM`: the shape operator is tangent-valued. -/
theorem shapeOperator_mem (η X : SmoothVectorField I M) (p : M) :
    D.shapeOperator nabla η X p ∈ D.tang p := by
  rw [shapeOperator, SmoothVectorField.neg_apply]
  exact neg_mem (D.tangentProj_mem _ p)

omit [CompleteSpace E] in
theorem isTangentField_shapeOperator (η X : SmoothVectorField I M) :
    D.IsTangentField (D.shapeOperator nabla η X) :=
  D.shapeOperator_mem nabla η X

omit [CompleteSpace E] in
/-- **Math.** `∇^⊥_X η (p) ∈ (T_pM)^⊥`: the normal connection is normal-valued. -/
theorem normalCov_mem (X η : SmoothVectorField I M) (p : M) :
    D.normalCov nabla X η p ∈ D.normalSpace p :=
  D.normalProj_mem _ p

omit [CompleteSpace E] in
theorem isNormalField_normalCov (X η : SmoothVectorField I M) :
    D.IsNormalField (D.normalCov nabla X η) :=
  D.normalCov_mem nabla X η

/-! ### Connection laws of the normal connection

do Carmo Ch. 6 §3: "the normal connection `∇^⊥` possesses the usual properties
of a connection": `𝒟(M̄)`-linearity in the direction slot, additivity in `η`,
and the Leibniz rule on normal fields. -/

omit [CompleteSpace E] in
/-- **Math.** Additivity of `∇^⊥` in the direction slot. -/
theorem normalCov_add_left (X₁ X₂ η : SmoothVectorField I M) :
    D.normalCov nabla (X₁ + X₂) η
      = D.normalCov nabla X₁ η + D.normalCov nabla X₂ η := by
  simp only [normalCov, nabla.add_left, D.normalProj_add]

omit [CompleteSpace E] in
/-- **Math.** `𝒟`-homogeneity of `∇^⊥` in the direction slot:
`∇^⊥_{fX} η = f ∇^⊥_X η`. -/
theorem normalCov_smul_left {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X η : SmoothVectorField I M) :
    D.normalCov nabla (SmoothVectorField.smul f hf X) η
      = SmoothVectorField.smul f hf (D.normalCov nabla X η) := by
  simp only [normalCov, nabla.smul_left, D.normalProj_smul]

omit [CompleteSpace E] in
/-- **Math.** Additivity of `∇^⊥` in `η`. -/
theorem normalCov_add_right (X η₁ η₂ : SmoothVectorField I M) :
    D.normalCov nabla X (η₁ + η₂)
      = D.normalCov nabla X η₁ + D.normalCov nabla X η₂ := by
  simp only [normalCov, nabla.add_right, D.normalProj_add]

omit [CompleteSpace E] in
/-- **Math.** The Leibniz rule of the normal connection on a *normal* field:
`∇^⊥_X (fη) = f ∇^⊥_X η + X(f) η`. (Normality of `η` keeps the first-order term
`X(f) η` inside the normal spaces.) -/
theorem normalCov_smul_right {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : SmoothVectorField I M) {η : SmoothVectorField I M}
    (hη : D.IsNormalField η) :
    D.normalCov nabla X (SmoothVectorField.smul f hf η)
      = SmoothVectorField.smul f hf (D.normalCov nabla X η)
        + SmoothVectorField.smul (X.dir f) (X.dir_contMDiff hf) η := by
  simp only [normalCov]
  rw [nabla.cov_smul_right hf X η, D.normalProj_add, D.normalProj_smul,
    D.normalProj_smul, hη.normalProj_eq]

/-! ### The Weingarten pairing and self-adjointness

The field-level content of do Carmo's Def. 2.2 and Prop. 2.3: for `Y` tangent
and `η` normal, `⟨S_η(X), Y⟩ = ⟨B(X, Y), η⟩`, by compatibility of `∇̄` with the
metric and `⟨η, Y⟩ ≡ 0`. -/

omit [CompleteSpace E] in
/-- **Math.** The **Weingarten pairing** (do Carmo Ch. 6, Def. 2.2/Prop. 2.3 at
the level of fields): for `Y` tangent and `η` normal,
`⟨S_η(X), Y⟩ = ⟨B(X, Y), η⟩` at every point. -/
theorem inner_shapeOperator_apply (hcompat : nabla.IsMetricCompatible g)
    (X : SmoothVectorField I M) {Y η : SmoothVectorField I M}
    (hY : D.IsTangentField Y) (hη : D.IsNormalField η) (p : M) :
    g.metricInner p (D.shapeOperator nabla η X p) (Y p)
      = g.metricInner p (D.secondFundForm nabla X Y p) (η p) := by
  have hzero : (fun q => g.metricInner q (η q) (Y q)) = fun _ => (0 : ℝ) :=
    funext fun q =>
      D.inner_eq_zero_of_mem_normalSpace_of_mem_tang (hη q) (hY q)
  have hdir : X.dir (fun q => g.metricInner q (η q) (Y q)) p = 0 := by
    rw [hzero]
    simp only [SmoothVectorField.dir, mfderiv_const]
    rfl
  have hc := hcompat X η Y p
  rw [hdir] at hc
  -- split `∇̄_X η` into `−S_η(X) + ∇^⊥_X η`
  have hsplit₁ := congrArg (fun F : SmoothVectorField I M => F p)
    (D.cov_eq_neg_shapeOperator_add_normalCov nabla X η)
  simp only [SmoothVectorField.add_apply, SmoothVectorField.neg_apply] at hsplit₁
  -- split `∇̄_X Y` into `∇_X Y + B(X, Y)`
  have hsplit₂ := congrArg (fun F : SmoothVectorField I M => F p)
    (D.cov_eq_inducedCov_add_secondFundForm nabla X Y)
  simp only [SmoothVectorField.add_apply] at hsplit₂
  rw [hsplit₁, hsplit₂, g.metricInner_add_left, g.metricInner_neg_left,
    g.metricInner_add_right,
    D.inner_eq_zero_of_mem_normalSpace_of_mem_tang
      (D.normalCov_mem nabla X η p) (hY p),
    D.inner_eq_zero_of_mem_normalSpace_of_mem_tang (hη p)
      (D.isTangentField_inducedCov nabla X Y p),
    g.metricInner_comm p (η p)] at hc
  linarith

/-- **Math.** **Self-adjointness of the shape operator** (do Carmo Ch. 6,
Def. 2.2): for tangent `X, Y` and normal `η`, `⟨S_η(X), Y⟩ = ⟨X, S_η(Y)⟩`, via
the Weingarten pairing and the symmetry of `B`. -/
theorem inner_shapeOperator_symm (hLC : nabla.IsLeviCivita g)
    {X Y η : SmoothVectorField I M} (hX : D.IsTangentField X)
    (hY : D.IsTangentField Y) (hη : D.IsNormalField η) (p : M) :
    g.metricInner p (D.shapeOperator nabla η X p) (Y p)
      = g.metricInner p (X p) (D.shapeOperator nabla η Y p) := by
  rw [D.inner_shapeOperator_apply nabla hLC.2 X hY hη p,
    D.secondFundForm_symm nabla hLC.1 hX hY,
    ← D.inner_shapeOperator_apply nabla hLC.2 Y hX hη p,
    g.metricInner_comm]

/-! ### The curvature operators of the induced and normal connections -/

/-- **Math.** The **curvature of the induced connection**,
`R(X,Y)Z = ∇_Y ∇_X Z − ∇_X ∇_Y Z + ∇_{[X,Y]} Z` (do Carmo's sign convention,
mirroring `AffineConnection.curvature`). On tangent fields this is the
curvature of the immersed manifold. -/
def inducedCurvature (X Y Z : SmoothVectorField I M) : SmoothVectorField I M :=
  D.inducedCov nabla Y (D.inducedCov nabla X Z)
    - D.inducedCov nabla X (D.inducedCov nabla Y Z)
    + D.inducedCov nabla (bracketField X Y) Z

theorem inducedCurvature_apply (X Y Z : SmoothVectorField I M) (p : M) :
    D.inducedCurvature nabla X Y Z p
      = D.inducedCov nabla Y (D.inducedCov nabla X Z) p
        - D.inducedCov nabla X (D.inducedCov nabla Y Z) p
        + D.inducedCov nabla (bracketField X Y) Z p := by
  simp only [inducedCurvature, SmoothVectorField.sub_apply,
    SmoothVectorField.add_apply]

/-- **Math.** `R(X,Y)Z(p) ∈ T_pM`: the induced curvature is tangent-valued. -/
theorem inducedCurvature_mem (X Y Z : SmoothVectorField I M) (p : M) :
    D.inducedCurvature nabla X Y Z p ∈ D.tang p := by
  rw [inducedCurvature, SmoothVectorField.add_apply, SmoothVectorField.sub_apply]
  exact add_mem (sub_mem (D.tangentProj_mem _ p) (D.tangentProj_mem _ p))
    (D.tangentProj_mem _ p)

/-- **Math.** do Carmo Ch. 6 §3: the **normal curvature** of the immersion,
`R^⊥(X,Y)η = ∇^⊥_Y ∇^⊥_X η − ∇^⊥_X ∇^⊥_Y η + ∇^⊥_{[X,Y]} η`. -/
def normalCurvature (X Y η : SmoothVectorField I M) : SmoothVectorField I M :=
  D.normalCov nabla Y (D.normalCov nabla X η)
    - D.normalCov nabla X (D.normalCov nabla Y η)
    + D.normalCov nabla (bracketField X Y) η

theorem normalCurvature_apply (X Y η : SmoothVectorField I M) (p : M) :
    D.normalCurvature nabla X Y η p
      = D.normalCov nabla Y (D.normalCov nabla X η) p
        - D.normalCov nabla X (D.normalCov nabla Y η) p
        + D.normalCov nabla (bracketField X Y) η p := by
  simp only [normalCurvature, SmoothVectorField.sub_apply,
    SmoothVectorField.add_apply]

/-- **Math.** `R^⊥(X,Y)η(p) ∈ (T_pM)^⊥`: the normal curvature is
normal-valued. -/
theorem normalCurvature_mem (X Y η : SmoothVectorField I M) (p : M) :
    D.normalCurvature nabla X Y η p ∈ D.normalSpace p := by
  rw [normalCurvature, SmoothVectorField.add_apply, SmoothVectorField.sub_apply]
  exact add_mem (sub_mem (D.normalProj_mem _ p) (D.normalProj_mem _ p))
    (D.normalProj_mem _ p)

/-! ### The decomposition of the ambient curvature (do Carmo eq. (6)) -/

/-- **Math.** do Carmo Ch. 6 §3, equation (6): the decomposition of the ambient
curvature applied to a field `Z`,

`R̄(X,Y)Z = R(X,Y)Z + B(Y, ∇_X Z) − B(X, ∇_Y Z) + B([X,Y], Z)
  − S_{B(X,Z)}(Y) + S_{B(Y,Z)}(X) + ∇^⊥_Y B(X,Z) − ∇^⊥_X B(Y,Z)`,

obtained by splitting each ambient covariant derivative into its tangential and
normal parts. A pure bookkeeping identity — no tangency hypotheses are
needed. -/
theorem curvature_decomposition (X Y Z : SmoothVectorField I M) (p : M) :
    nabla.curvature X Y Z p
      = D.inducedCurvature nabla X Y Z p
        + D.secondFundForm nabla Y (D.inducedCov nabla X Z) p
        - D.secondFundForm nabla X (D.inducedCov nabla Y Z) p
        + D.secondFundForm nabla (bracketField X Y) Z p
        - D.shapeOperator nabla (D.secondFundForm nabla X Z) Y p
        + D.shapeOperator nabla (D.secondFundForm nabla Y Z) X p
        + D.normalCov nabla Y (D.secondFundForm nabla X Z) p
        - D.normalCov nabla X (D.secondFundForm nabla Y Z) p := by
  have e1 : nabla.cov Y (nabla.cov X Z)
      = nabla.cov Y (D.inducedCov nabla X Z)
        + nabla.cov Y (D.secondFundForm nabla X Z) := by
    conv_lhs => rw [D.cov_eq_inducedCov_add_secondFundForm nabla X Z]
    rw [nabla.add_right]
  have e2 : nabla.cov X (nabla.cov Y Z)
      = nabla.cov X (D.inducedCov nabla Y Z)
        + nabla.cov X (D.secondFundForm nabla Y Z) := by
    conv_lhs => rw [D.cov_eq_inducedCov_add_secondFundForm nabla Y Z]
    rw [nabla.add_right]
  have h1 := congrArg (fun F : SmoothVectorField I M => F p) e1
  have h2 := congrArg (fun F : SmoothVectorField I M => F p) e2
  have d1 := congrArg (fun F : SmoothVectorField I M => F p)
    (D.cov_eq_inducedCov_add_secondFundForm nabla Y (D.inducedCov nabla X Z))
  have d2 := congrArg (fun F : SmoothVectorField I M => F p)
    (D.cov_eq_inducedCov_add_secondFundForm nabla X (D.inducedCov nabla Y Z))
  have d3 := congrArg (fun F : SmoothVectorField I M => F p)
    (D.cov_eq_neg_shapeOperator_add_normalCov nabla Y
      (D.secondFundForm nabla X Z))
  have d4 := congrArg (fun F : SmoothVectorField I M => F p)
    (D.cov_eq_neg_shapeOperator_add_normalCov nabla X
      (D.secondFundForm nabla Y Z))
  have d5 := congrArg (fun F : SmoothVectorField I M => F p)
    (D.cov_eq_inducedCov_add_secondFundForm nabla (bracketField X Y) Z)
  simp only [SmoothVectorField.add_apply, SmoothVectorField.neg_apply]
    at h1 h2 d1 d2 d3 d4 d5
  rw [nabla.curvature_apply, D.inducedCurvature_apply]
  linear_combination (norm := module) h1 - h2 + d1 - d2 + d3 - d4 + d5

/-- **Math.** The normal-argument analogue of equation (6) (do Carmo Ch. 6 §3,
display in the proof of Prop. 3.1): the decomposition of the ambient curvature
applied to a field `η`, in Weingarten terms,

`R̄(X,Y)η = R^⊥(X,Y)η − S_{∇^⊥_X η}(Y) + S_{∇^⊥_Y η}(X)
  − ∇_Y(S_η X) + ∇_X(S_η Y) − B(Y, S_η X) + B(X, S_η Y) − S_η([X,Y])`.

Again a pure bookkeeping identity. -/
theorem curvature_normal_decomposition (X Y η : SmoothVectorField I M) (p : M) :
    nabla.curvature X Y η p
      = D.normalCurvature nabla X Y η p
        - D.shapeOperator nabla (D.normalCov nabla X η) Y p
        + D.shapeOperator nabla (D.normalCov nabla Y η) X p
        - D.inducedCov nabla Y (D.shapeOperator nabla η X) p
        + D.inducedCov nabla X (D.shapeOperator nabla η Y) p
        - D.secondFundForm nabla Y (D.shapeOperator nabla η X) p
        + D.secondFundForm nabla X (D.shapeOperator nabla η Y) p
        - D.shapeOperator nabla η (bracketField X Y) p := by
  have e1 : nabla.cov Y (nabla.cov X η)
      = nabla.cov Y (-(D.shapeOperator nabla η X))
        + nabla.cov Y (D.normalCov nabla X η) := by
    conv_lhs => rw [D.cov_eq_neg_shapeOperator_add_normalCov nabla X η]
    rw [nabla.add_right]
  have e2 : nabla.cov X (nabla.cov Y η)
      = nabla.cov X (-(D.shapeOperator nabla η Y))
        + nabla.cov X (D.normalCov nabla Y η) := by
    conv_lhs => rw [D.cov_eq_neg_shapeOperator_add_normalCov nabla Y η]
    rw [nabla.add_right]
  have h1 := congrArg (fun F : SmoothVectorField I M => F p) e1
  have h2 := congrArg (fun F : SmoothVectorField I M => F p) e2
  -- negations under the connection, pointwise
  have n1 := nabla.cov_neg_right Y (D.shapeOperator nabla η X) p
  have n2 := nabla.cov_neg_right X (D.shapeOperator nabla η Y) p
  -- splittings of the four remaining covariant derivatives
  have d1 := congrArg (fun F : SmoothVectorField I M => F p)
    (D.cov_eq_inducedCov_add_secondFundForm nabla Y (D.shapeOperator nabla η X))
  have d2 := congrArg (fun F : SmoothVectorField I M => F p)
    (D.cov_eq_inducedCov_add_secondFundForm nabla X (D.shapeOperator nabla η Y))
  have d3 := congrArg (fun F : SmoothVectorField I M => F p)
    (D.cov_eq_neg_shapeOperator_add_normalCov nabla Y (D.normalCov nabla X η))
  have d4 := congrArg (fun F : SmoothVectorField I M => F p)
    (D.cov_eq_neg_shapeOperator_add_normalCov nabla X (D.normalCov nabla Y η))
  have d5 := congrArg (fun F : SmoothVectorField I M => F p)
    (D.cov_eq_neg_shapeOperator_add_normalCov nabla (bracketField X Y) η)
  simp only [SmoothVectorField.add_apply, SmoothVectorField.neg_apply]
    at h1 h2 d1 d2 d3 d4 d5
  rw [nabla.curvature_apply, D.normalCurvature_apply]
  linear_combination (norm := module) h1 - h2 + n1 - n2 - d1 + d2 + d3 - d4 + d5

/-! ### The Gauss and Ricci equations (do Carmo Ch. 6, Prop. 3.1) -/

/-- **Math.** do Carmo Ch. 6, Prop. 3.1(a) — the **Gauss equation**:

`⟨R̄(X,Y)Z, T⟩ = ⟨R(X,Y)Z, T⟩ − ⟨B(Y,T), B(X,Z)⟩ + ⟨B(X,T), B(Y,Z)⟩`

for `T` tangent (do Carmo states it for all of `X, Y, Z, T` tangent; only
tangency of the test field is needed). Pairing the decomposition (6) with `T`
kills the normal terms, and the Weingarten pairing converts the two shape
operator terms. -/
theorem gauss_equation (hcompat : nabla.IsMetricCompatible g)
    (X Y Z : SmoothVectorField I M) {T : SmoothVectorField I M}
    (hT : D.IsTangentField T) (p : M) :
    g.metricInner p (nabla.curvature X Y Z p) (T p)
      = g.metricInner p (D.inducedCurvature nabla X Y Z p) (T p)
        - g.metricInner p (D.secondFundForm nabla Y T p)
            (D.secondFundForm nabla X Z p)
        + g.metricInner p (D.secondFundForm nabla X T p)
            (D.secondFundForm nabla Y Z p) := by
  rw [D.curvature_decomposition nabla X Y Z p]
  simp only [g.metricInner_add_left, g.metricInner_sub_left]
  rw [D.inner_eq_zero_of_mem_normalSpace_of_mem_tang
      (D.secondFundForm_mem nabla Y (D.inducedCov nabla X Z) p) (hT p),
    D.inner_eq_zero_of_mem_normalSpace_of_mem_tang
      (D.secondFundForm_mem nabla X (D.inducedCov nabla Y Z) p) (hT p),
    D.inner_eq_zero_of_mem_normalSpace_of_mem_tang
      (D.secondFundForm_mem nabla (bracketField X Y) Z p) (hT p),
    D.inner_eq_zero_of_mem_normalSpace_of_mem_tang
      (D.normalCov_mem nabla Y (D.secondFundForm nabla X Z) p) (hT p),
    D.inner_eq_zero_of_mem_normalSpace_of_mem_tang
      (D.normalCov_mem nabla X (D.secondFundForm nabla Y Z) p) (hT p),
    D.inner_shapeOperator_apply nabla hcompat Y hT
      (D.isNormalField_secondFundForm nabla X Z) p,
    D.inner_shapeOperator_apply nabla hcompat X hT
      (D.isNormalField_secondFundForm nabla Y Z) p]
  ring

/-- **Math.** do Carmo Ch. 6, Prop. 3.1(b) — the **Ricci equation**:

`⟨R̄(X,Y)η, ζ⟩ − ⟨R^⊥(X,Y)η, ζ⟩ = ⟨[S_η, S_ζ]X, Y⟩`

for `X, Y` tangent and `η, ζ` normal, where `[S_η, S_ζ] = S_η∘S_ζ − S_ζ∘S_η`.
Pairing the normal decomposition of `R̄(X,Y)η` with `ζ` kills the tangential
terms; the two remaining `B`-terms become the commutator through the Weingarten
pairing and the self-adjointness of the shape operators. -/
theorem ricci_equation (hLC : nabla.IsLeviCivita g)
    (X : SmoothVectorField I M) {Y η ζ : SmoothVectorField I M}
    (hY : D.IsTangentField Y) (hη : D.IsNormalField η)
    (hζ : D.IsNormalField ζ) (p : M) :
    g.metricInner p (nabla.curvature X Y η p) (ζ p)
      - g.metricInner p (D.normalCurvature nabla X Y η p) (ζ p)
      = g.metricInner p
          ((D.shapeOperator nabla η (D.shapeOperator nabla ζ X)
            - D.shapeOperator nabla ζ (D.shapeOperator nabla η X)) p) (Y p) := by
  rw [D.curvature_normal_decomposition nabla X Y η p]
  simp only [g.metricInner_add_left, g.metricInner_sub_left]
  rw [D.inner_eq_zero_of_mem_tang_of_mem_normalSpace
      (D.shapeOperator_mem nabla (D.normalCov nabla X η) Y p) (hζ p),
    D.inner_eq_zero_of_mem_tang_of_mem_normalSpace
      (D.shapeOperator_mem nabla (D.normalCov nabla Y η) X p) (hζ p),
    D.inner_eq_zero_of_mem_tang_of_mem_normalSpace
      (D.isTangentField_inducedCov nabla Y (D.shapeOperator nabla η X) p) (hζ p),
    D.inner_eq_zero_of_mem_tang_of_mem_normalSpace
      (D.isTangentField_inducedCov nabla X (D.shapeOperator nabla η Y) p) (hζ p),
    D.inner_eq_zero_of_mem_tang_of_mem_normalSpace
      (D.shapeOperator_mem nabla η (bracketField X Y) p) (hζ p)]
  -- convert the two `B`-terms via the Weingarten pairing …
  rw [← D.inner_shapeOperator_apply nabla hLC.2 Y
      (D.isTangentField_shapeOperator nabla η X) hζ p,
    ← D.inner_shapeOperator_apply nabla hLC.2 X
      (D.isTangentField_shapeOperator nabla η Y) hζ p]
  -- … and re-associate through self-adjointness of `S_η`, `S_ζ`
  have hsa₁ : g.metricInner p (D.shapeOperator nabla ζ X p)
        (D.shapeOperator nabla η Y p)
      = g.metricInner p
          (D.shapeOperator nabla η (D.shapeOperator nabla ζ X) p) (Y p) :=
    (D.inner_shapeOperator_symm nabla hLC
      (D.isTangentField_shapeOperator nabla ζ X) hY hη p).symm
  have hsa₂ : g.metricInner p (D.shapeOperator nabla ζ Y p)
        (D.shapeOperator nabla η X p)
      = g.metricInner p
          (D.shapeOperator nabla ζ (D.shapeOperator nabla η X) p) (Y p) := by
    rw [g.metricInner_comm p (D.shapeOperator nabla ζ Y p)
        (D.shapeOperator nabla η X p),
      ← D.inner_shapeOperator_symm nabla hLC
        (D.isTangentField_shapeOperator nabla η X) hY hζ p]
  rw [SmoothVectorField.sub_apply, g.metricInner_sub_left]
  linarith [hsa₁, hsa₂]

/-! ### The covariant derivative of `B` and the Codazzi equation
(do Carmo Ch. 6, Rem. 3.3 and Prop. 3.4) -/

/-- **Math.** do Carmo Ch. 6, Rem. 3.3: the second fundamental form regarded as
a scalar tensor, `B(X, Y, η) = ⟨B(X, Y), η⟩`. -/
def secondFundTensor (X Y η : SmoothVectorField I M) : M → ℝ :=
  fun p => g.metricInner p (D.secondFundForm nabla X Y p) (η p)

/-- **Math.** do Carmo Ch. 6, Rem. 3.3: the **covariant derivative of the
second fundamental form**,

`(∇̄_X B)(Y, Z, η) = X(B(Y, Z, η)) − B(∇_X Y, Z, η) − B(Y, ∇_X Z, η)
  − B(Y, Z, ∇^⊥_X η)`. -/
def secondFundTensorCovDeriv (X Y Z η : SmoothVectorField I M) : M → ℝ :=
  fun p => X.dir (D.secondFundTensor nabla Y Z η) p
    - D.secondFundTensor nabla (D.inducedCov nabla X Y) Z η p
    - D.secondFundTensor nabla Y (D.inducedCov nabla X Z) η p
    - D.secondFundTensor nabla Y Z (D.normalCov nabla X η) p

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 6, proof of Prop. 3.4, first display: for `η`
normal, the covariant derivative of the tensor `B` reduces to

`(∇̄_X B)(Y, Z, η) = ⟨∇^⊥_X(B(Y, Z)), η⟩ − B(∇_X Y, Z, η) − B(Y, ∇_X Z, η)`,

by compatibility of `∇̄` with the metric and orthogonality of the splitting. -/
theorem secondFundTensorCovDeriv_eq (hcompat : nabla.IsMetricCompatible g)
    (X Y Z : SmoothVectorField I M) {η : SmoothVectorField I M}
    (hη : D.IsNormalField η) (p : M) :
    D.secondFundTensorCovDeriv nabla X Y Z η p
      = g.metricInner p
          (D.normalCov nabla X (D.secondFundForm nabla Y Z) p) (η p)
        - D.secondFundTensor nabla (D.inducedCov nabla X Y) Z η p
        - D.secondFundTensor nabla Y (D.inducedCov nabla X Z) η p := by
  have hc := hcompat X (D.secondFundForm nabla Y Z) η p
  -- split `∇̄_X (B(Y,Z))` and `∇̄_X η`
  have hs₁ := congrArg (fun F : SmoothVectorField I M => F p)
    (D.cov_eq_neg_shapeOperator_add_normalCov nabla X
      (D.secondFundForm nabla Y Z))
  have hs₂ := congrArg (fun F : SmoothVectorField I M => F p)
    (D.cov_eq_neg_shapeOperator_add_normalCov nabla X η)
  simp only [SmoothVectorField.add_apply, SmoothVectorField.neg_apply] at hs₁ hs₂
  rw [hs₁, hs₂, g.metricInner_add_left, g.metricInner_neg_left,
    g.metricInner_add_right, g.metricInner_neg_right,
    D.inner_eq_zero_of_mem_tang_of_mem_normalSpace
      (D.shapeOperator_mem nabla (D.secondFundForm nabla Y Z) X p) (hη p),
    D.inner_eq_zero_of_mem_normalSpace_of_mem_tang
      (D.secondFundForm_mem nabla Y Z p)
      (D.shapeOperator_mem nabla η X p)] at hc
  simp only [secondFundTensorCovDeriv, secondFundTensor]
  have hdir : X.dir (D.secondFundTensor nabla Y Z η) p
      = X.dir (fun q => g.metricInner q (D.secondFundForm nabla Y Z q) (η q)) p :=
    rfl
  rw [hdir, hc]
  ring

/-- **Math.** do Carmo Ch. 6, Prop. 3.4 — the **Codazzi equation**:

`⟨R̄(X,Y)Z, η⟩ = (∇̄_Y B)(X, Z, η) − (∇̄_X B)(Y, Z, η)`

for `X, Y` tangent and `η` normal. Pairing the decomposition (6) with `η` kills
the tangential terms; the reduced form of `(∇̄B)` and the symmetry
`[X,Y] = ∇_X Y − ∇_Y X` of the induced connection assemble the rest. -/
theorem codazzi_equation (hLC : nabla.IsLeviCivita g)
    {X Y : SmoothVectorField I M} (Z : SmoothVectorField I M)
    {η : SmoothVectorField I M} (hX : D.IsTangentField X)
    (hY : D.IsTangentField Y) (hη : D.IsNormalField η) (p : M) :
    g.metricInner p (nabla.curvature X Y Z p) (η p)
      = D.secondFundTensorCovDeriv nabla Y X Z η p
        - D.secondFundTensorCovDeriv nabla X Y Z η p := by
  -- `B([X,Y], Z) = B(∇_X Y, Z) − B(∇_Y X, Z)` from symmetry of `∇`
  have hbr : D.secondFundForm nabla (bracketField X Y) Z
      = D.secondFundForm nabla (D.inducedCov nabla X Y) Z
        - D.secondFundForm nabla (D.inducedCov nabla Y X) Z := by
    rw [← D.secondFundForm_sub_left nabla, ← D.inducedCov_sub_swap nabla hLC.1 hX hY]
  have hbr' := congrArg
    (fun F : SmoothVectorField I M => g.metricInner p (F p) (η p)) hbr
  simp only [SmoothVectorField.sub_apply, g.metricInner_sub_left] at hbr'
  rw [D.curvature_decomposition nabla X Y Z p]
  simp only [g.metricInner_add_left, g.metricInner_sub_left]
  rw [D.inner_eq_zero_of_mem_tang_of_mem_normalSpace
      (D.inducedCurvature_mem nabla X Y Z p) (hη p),
    D.inner_eq_zero_of_mem_tang_of_mem_normalSpace
      (D.shapeOperator_mem nabla (D.secondFundForm nabla X Z) Y p) (hη p),
    D.inner_eq_zero_of_mem_tang_of_mem_normalSpace
      (D.shapeOperator_mem nabla (D.secondFundForm nabla Y Z) X p) (hη p),
    D.secondFundTensorCovDeriv_eq nabla hLC.2 Y X Z hη p,
    D.secondFundTensorCovDeriv_eq nabla hLC.2 X Y Z hη p]
  simp only [secondFundTensor]
  linarith [hbr']

end DCImmersedPatch

end Riemannian
