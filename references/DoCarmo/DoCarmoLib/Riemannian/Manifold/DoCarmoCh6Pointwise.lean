import DoCarmoLib.Riemannian.Manifold.DoCarmoCh6Locality

/-!
# do Carmo Chapter 6 §2 — the pointwise second fundamental form and shape operator

The pointwise layer of `def:dc-ch6-2-2` and `prop:dc-ch6-2-3`. By the locality
of `B` (`secondFundForm_congr_apply`), the value `B(X,Y)(p)` depends only on
`x = X(p)` and `y = Y(p)`, so for `p ∈ M̄` and vectors `x, y ∈ T_pM`,
`η ∈ (T_pM)^⊥` we may define

* `secondFundFormAt p x y` — the vector `B(x, y) ∈ (T_pM)^⊥`, via (arbitrary,
  chosen) extensions of `x` and of the tangential part of `y`;
* `secondFundScalarAt p η x y` — do Carmo's symmetric bilinear form
  `H_η(x, y) = ⟨B(x, y), η⟩`;
* `secondFundQuadAt p η x` — the **second fundamental form**
  `II_η(x) = H_η(x, x)` of the immersion at `p` along `η`;
* `shapeOperatorAt p η x` — the **self-adjoint operator** `S_η : T_pM → T_pM`
  determined by `⟨S_η(x), y⟩ = H_η(x, y)` (`inner_shapeOperatorAt`,
  `inner_shapeOperatorAt_symm`);

and prove do Carmo's Prop. 2.3 (`shapeOperatorAt_eq_shapeOperator`): for *any*
local extension `N` of `η` normal to `M`, `S_η(x) = −(∇̄_x N)ᵀ` — the value is
independent of the chosen extension.

Reference: do Carmo, *Riemannian Geometry*, Ch. 6 §2, Def. 2.2 and Prop. 2.3.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Chosen extensions of tangent vectors -/

omit [CompleteSpace E] in
/-- **Math.** A chosen global smooth extension of a tangent vector: a smooth
field whose value at `p` is `v` (do Carmo Ch. 0/2; existence by bump-function
extension). -/
noncomputable def vectorFieldExtension (p : M) (v : TangentSpace I p) :
    SmoothVectorField I M :=
  (exists_smoothVectorField_eq p v).choose

omit [CompleteSpace E] in
@[simp] theorem vectorFieldExtension_apply_self (p : M) (v : TangentSpace I p) :
    vectorFieldExtension p v p = v :=
  (exists_smoothVectorField_eq p v).choose_spec

namespace DCImmersedPatch

variable {g : RiemannianMetric I M} (D : DCImmersedPatch I M g)

omit [CompleteSpace E] in
/-- **Math.** The chosen *tangent* extension of a vector: the tangential
projection of a chosen extension. For `v ∈ T_pM` its value at `p` is `v`. -/
noncomputable def tangentExtension (p : M) (v : TangentSpace I p) :
    SmoothVectorField I M :=
  D.tangentProj (vectorFieldExtension p v)

omit [CompleteSpace E] in
theorem isTangentField_tangentExtension (p : M) (v : TangentSpace I p) :
    D.IsTangentField (D.tangentExtension p v) :=
  D.tangentProj_mem _

omit [CompleteSpace E] in
theorem tangentExtension_apply_self {p : M} {v : TangentSpace I p}
    (hv : v ∈ D.tang p) : D.tangentExtension p v p = v := by
  have h : vectorFieldExtension p v p ∈ D.tang p := by
    rw [vectorFieldExtension_apply_self]; exact hv
  rw [tangentExtension, D.tangentProj_apply_of_mem h,
    vectorFieldExtension_apply_self]

omit [CompleteSpace E] in
/-- **Math.** The chosen *normal* extension of a vector: the normal projection
of a chosen extension. For `η ∈ (T_pM)^⊥` its value at `p` is `η`. -/
noncomputable def normalExtension (p : M) (v : TangentSpace I p) :
    SmoothVectorField I M :=
  D.normalProj (vectorFieldExtension p v)

omit [CompleteSpace E] in
theorem isNormalField_normalExtension (p : M) (v : TangentSpace I p) :
    D.IsNormalField (D.normalExtension p v) :=
  D.normalProj_mem _

omit [CompleteSpace E] in
theorem normalExtension_apply_self {p : M} {v : TangentSpace I p}
    (hv : v ∈ D.normalSpace p) : D.normalExtension p v p = v := by
  have h : vectorFieldExtension p v p ∈ D.normalSpace p := by
    rw [vectorFieldExtension_apply_self]; exact hv
  rw [normalExtension, normalProj_apply,
    D.tangentProj_apply_of_mem_normalSpace h, vectorFieldExtension_apply_self,
    sub_zero]

/-! ### The pointwise second fundamental form -/

variable (nabla : AffineConnection I M)

/-- **Math.** do Carmo Ch. 6 §2 (after Prop. 2.1): the **pointwise second
fundamental form** `B(x, y) ∈ (T_pM)^⊥` for `x, y ∈ T_pM̄`, defined through
(chosen) extensions — well-defined by the locality of `B`
(`secondFundForm_congr_apply`). In the second slot the tangential part of `y`
is used, so for `y ∈ T_pM` this is do Carmo's `B(x, y)`. -/
noncomputable def secondFundFormAt (p : M) (x y : TangentSpace I p) :
    TangentSpace I p :=
  D.secondFundForm nabla (vectorFieldExtension p x) (D.tangentExtension p y) p

omit [CompleteSpace E] in
/-- **Math.** The pointwise form evaluates fields: for `Y` tangent,
`B(X(p), Y(p)) = B(X, Y)(p)`. This is the well-definedness statement — the
choice of extensions does not matter. -/
theorem secondFundFormAt_apply_apply {Y : SmoothVectorField I M}
    (hY : D.IsTangentField Y) (X : SmoothVectorField I M) (p : M) :
    D.secondFundFormAt nabla p (X p) (Y p) = D.secondFundForm nabla X Y p :=
  D.secondFundForm_congr_apply nabla
    (D.isTangentField_tangentExtension p (Y p)) hY
    (vectorFieldExtension_apply_self p (X p))
    (D.tangentExtension_apply_self (hY p))

omit [CompleteSpace E] in
/-- **Math.** `B(x, y) ∈ (T_pM)^⊥`. -/
theorem secondFundFormAt_mem (p : M) (x y : TangentSpace I p) :
    D.secondFundFormAt nabla p x y ∈ D.normalSpace p :=
  D.secondFundForm_mem nabla _ _ p

omit [CompleteSpace E] in
/-- **Math.** Additivity of the pointwise `B` in the first slot. -/
theorem secondFundFormAt_add_left (p : M) (x₁ x₂ y : TangentSpace I p) :
    D.secondFundFormAt nabla p (x₁ + x₂) y
      = D.secondFundFormAt nabla p x₁ y + D.secondFundFormAt nabla p x₂ y := by
  have hcongr : D.secondFundFormAt nabla p (x₁ + x₂) y
      = D.secondFundForm nabla
          (vectorFieldExtension p x₁ + vectorFieldExtension p x₂)
          (D.tangentExtension p y) p :=
    D.secondFundForm_congr_apply nabla
      (D.isTangentField_tangentExtension p y)
      (D.isTangentField_tangentExtension p y)
      (by simp) rfl
  rw [hcongr]
  have hadd := congrArg (fun F : SmoothVectorField I M => F p)
    (D.secondFundForm_add_left nabla (vectorFieldExtension p x₁)
      (vectorFieldExtension p x₂) (D.tangentExtension p y))
  simp only [SmoothVectorField.add_apply] at hadd
  exact hadd

omit [CompleteSpace E] in
/-- **Math.** Homogeneity of the pointwise `B` in the first slot. -/
theorem secondFundFormAt_smul_left (p : M) (c : ℝ) (x y : TangentSpace I p) :
    D.secondFundFormAt nabla p (c • x) y
      = c • D.secondFundFormAt nabla p x y := by
  have hcongr : D.secondFundFormAt nabla p (c • x) y
      = D.secondFundForm nabla (c • vectorFieldExtension p x)
          (D.tangentExtension p y) p :=
    D.secondFundForm_congr_apply nabla
      (D.isTangentField_tangentExtension p y)
      (D.isTangentField_tangentExtension p y)
      (by simp) rfl
  rw [hcongr]
  -- `c • X = smul (const c) X` and `B` is `𝒟`-homogeneous in the first slot
  have hsm : (c • vectorFieldExtension p x)
      = SmoothVectorField.smul (fun _ => c) contMDiff_const
          (vectorFieldExtension p x) := by
    ext q
    simp
  rw [hsm]
  have h := congrArg (fun F : SmoothVectorField I M => F p)
    (D.secondFundForm_smul_left nabla contMDiff_const (f := fun _ => c)
      (vectorFieldExtension p x) (D.tangentExtension p y))
  simp only [SmoothVectorField.smul_apply] at h
  exact h

omit [CompleteSpace E] in
/-- **Math.** Additivity of the pointwise `B` in the second slot. -/
theorem secondFundFormAt_add_right (p : M) (x y₁ y₂ : TangentSpace I p) :
    D.secondFundFormAt nabla p x (y₁ + y₂)
      = D.secondFundFormAt nabla p x y₁ + D.secondFundFormAt nabla p x y₂ := by
  have hval : D.tangentExtension p (y₁ + y₂) p
      = (D.tangentExtension p y₁ + D.tangentExtension p y₂) p := by
    rw [SmoothVectorField.add_apply, tangentExtension, tangentExtension,
      tangentExtension,
      D.tangentProj_congr_apply (Y := vectorFieldExtension p y₁
        + vectorFieldExtension p y₂) (by simp),
      D.tangentProj_add]
    simp
  have hcongr : D.secondFundFormAt nabla p x (y₁ + y₂)
      = D.secondFundForm nabla (vectorFieldExtension p x)
          (D.tangentExtension p y₁ + D.tangentExtension p y₂) p :=
    D.secondFundForm_congr_apply nabla
      (D.isTangentField_tangentExtension p (y₁ + y₂))
      (fun q => by
        rw [SmoothVectorField.add_apply]
        exact add_mem (D.isTangentField_tangentExtension p y₁ q)
          (D.isTangentField_tangentExtension p y₂ q))
      rfl hval
  rw [hcongr]
  have hadd := congrArg (fun F : SmoothVectorField I M => F p)
    (D.secondFundForm_add_right nabla (vectorFieldExtension p x)
      (D.tangentExtension p y₁) (D.tangentExtension p y₂))
  simp only [SmoothVectorField.add_apply] at hadd
  exact hadd

omit [CompleteSpace E] in
/-- **Math.** Homogeneity of the pointwise `B` in the second slot. -/
theorem secondFundFormAt_smul_right (p : M) (c : ℝ) (x y : TangentSpace I p) :
    D.secondFundFormAt nabla p x (c • y)
      = c • D.secondFundFormAt nabla p x y := by
  have hval : D.tangentExtension p (c • y) p
      = (c • D.tangentExtension p y) p := by
    rw [SmoothVectorField.constSMul_apply, tangentExtension, tangentExtension,
      D.tangentProj_congr_apply (Y := c • vectorFieldExtension p y) (by simp),
      D.tangentProj_constSMul]
    simp
  have hcongr : D.secondFundFormAt nabla p x (c • y)
      = D.secondFundForm nabla (vectorFieldExtension p x)
          (c • D.tangentExtension p y) p :=
    D.secondFundForm_congr_apply nabla
      (D.isTangentField_tangentExtension p (c • y))
      (fun q => by
        rw [SmoothVectorField.constSMul_apply]
        exact Submodule.smul_mem _ _ (D.isTangentField_tangentExtension p y q))
      rfl hval
  rw [hcongr]
  have hsm : (c • D.tangentExtension p y)
      = SmoothVectorField.smul (fun _ => c) contMDiff_const
          (D.tangentExtension p y) := by
    ext q
    simp
  rw [hsm]
  have h := congrArg (fun F : SmoothVectorField I M => F p)
    (D.secondFundForm_smul_right nabla contMDiff_const (f := fun _ => c)
      (vectorFieldExtension p x)
      (D.isTangentField_tangentExtension p y))
  simp only [SmoothVectorField.smul_apply] at h
  exact h

/-- **Math.** Symmetry of the pointwise `B` on tangent vectors (do Carmo
Prop. 2.1 read at a point). -/
theorem secondFundFormAt_symm (hsym : nabla.IsSymmetric) {p : M}
    {x y : TangentSpace I p} (hx : x ∈ D.tang p) (hy : y ∈ D.tang p) :
    D.secondFundFormAt nabla p x y = D.secondFundFormAt nabla p y x := by
  have h1 : D.secondFundFormAt nabla p x y
      = D.secondFundForm nabla (D.tangentExtension p x)
          (D.tangentExtension p y) p :=
    D.secondFundForm_congr_apply nabla
      (D.isTangentField_tangentExtension p y)
      (D.isTangentField_tangentExtension p y)
      (by rw [vectorFieldExtension_apply_self,
        D.tangentExtension_apply_self hx]) rfl
  have h2 : D.secondFundFormAt nabla p y x
      = D.secondFundForm nabla (D.tangentExtension p y)
          (D.tangentExtension p x) p :=
    D.secondFundForm_congr_apply nabla
      (D.isTangentField_tangentExtension p x)
      (D.isTangentField_tangentExtension p x)
      (by rw [vectorFieldExtension_apply_self,
        D.tangentExtension_apply_self hy]) rfl
  rw [h1, h2, D.secondFundForm_symm nabla hsym
    (D.isTangentField_tangentExtension p x)
    (D.isTangentField_tangentExtension p y)]

/-! ### `H_η`, `II_η` and the shape operator (do Carmo Def. 2.2) -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Vectors of `T_pM` are separated by their inner products against
`T_pM`. -/
theorem eq_of_inner_eq_of_mem_tang {p : M} {u v : TangentSpace I p}
    (hu : u ∈ D.tang p) (hv : v ∈ D.tang p)
    (h : ∀ w ∈ D.tang p, g.metricInner p u w = g.metricInner p v w) :
    u = v := by
  have hd : u - v ∈ D.tang p := sub_mem hu hv
  have hn : u - v ∈ D.normalSpace p := by
    rw [mem_normalSpace_iff]
    intro w hw
    rw [g.metricInner_comm, g.metricInner_sub_left, h w hw, sub_self]
  have h0 := D.eq_zero_of_mem_tang_of_mem_normalSpace hd hn
  exact sub_eq_zero.mp h0

/-- **Math.** do Carmo Ch. 6, Def. 2.2 (the bilinear form): for
`η ∈ (T_pM)^⊥`, the mapping `H_η(x, y) = ⟨B(x, y), η⟩` on `T_pM × T_pM` — a
symmetric bilinear form by Prop. 2.1. -/
noncomputable def secondFundScalarAt (p : M) (η x y : TangentSpace I p) : ℝ :=
  g.metricInner p (D.secondFundFormAt nabla p x y) η

/-- **Math.** do Carmo Ch. 6, Def. 2.2: the **second fundamental form** of `f`
at `p` along the normal vector `η` — the quadratic form
`II_η(x) = H_η(x, x)`. -/
noncomputable def secondFundQuadAt (p : M) (η x : TangentSpace I p) : ℝ :=
  D.secondFundScalarAt nabla p η x x

/-- **Math.** `H_η` is symmetric (do Carmo Def. 2.2). -/
theorem secondFundScalarAt_symm (hsym : nabla.IsSymmetric) {p : M}
    (η : TangentSpace I p) {x y : TangentSpace I p} (hx : x ∈ D.tang p)
    (hy : y ∈ D.tang p) :
    D.secondFundScalarAt nabla p η x y = D.secondFundScalarAt nabla p η y x := by
  rw [secondFundScalarAt, secondFundScalarAt,
    D.secondFundFormAt_symm nabla hsym hx hy]

/-- **Math.** do Carmo Ch. 6, Def. 2.2: the **shape operator** `S_η` at `p` —
the self-adjoint operator of `T_pM` associated to `H_η`, realized as
`S_η(x) = −(∇̄_x N)ᵀ` for the chosen normal extension `N` of `η` (any normal
extension gives the same value: Prop. 2.3, `shapeOperatorAt_eq_shapeOperator`). -/
noncomputable def shapeOperatorAt (p : M) (η x : TangentSpace I p) :
    TangentSpace I p :=
  D.shapeOperator nabla (D.normalExtension p η) (vectorFieldExtension p x) p

omit [CompleteSpace E] in
/-- **Math.** `S_η(x) ∈ T_pM`. -/
theorem shapeOperatorAt_mem (p : M) (η x : TangentSpace I p) :
    D.shapeOperatorAt nabla p η x ∈ D.tang p :=
  D.shapeOperator_mem nabla _ _ p

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 6, Def. 2.2, the defining property of the shape
operator: `⟨S_η(x), y⟩ = H_η(x, y) = ⟨B(x, y), η⟩` for `y ∈ T_pM` and
`η ∈ (T_pM)^⊥`. -/
theorem inner_shapeOperatorAt (hcompat : nabla.IsMetricCompatible g) {p : M}
    {η y : TangentSpace I p} (hη : η ∈ D.normalSpace p) (hy : y ∈ D.tang p)
    (x : TangentSpace I p) :
    g.metricInner p (D.shapeOperatorAt nabla p η x) y
      = D.secondFundScalarAt nabla p η x y := by
  have hpair := D.inner_shapeOperator_apply nabla hcompat
    (vectorFieldExtension p x) (D.isTangentField_tangentExtension p y)
    (D.isNormalField_normalExtension p η) p
  rw [D.tangentExtension_apply_self hy, D.normalExtension_apply_self hη]
    at hpair
  exact hpair

/-- **Math.** do Carmo Ch. 6, Def. 2.2: `S_η` is **self-adjoint**,
`⟨S_η(x), y⟩ = ⟨x, S_η(y)⟩` for `x, y ∈ T_pM`, `η ∈ (T_pM)^⊥`. -/
theorem inner_shapeOperatorAt_symm (hLC : nabla.IsLeviCivita g) {p : M}
    {η x y : TangentSpace I p} (hη : η ∈ D.normalSpace p) (hx : x ∈ D.tang p)
    (hy : y ∈ D.tang p) :
    g.metricInner p (D.shapeOperatorAt nabla p η x) y
      = g.metricInner p x (D.shapeOperatorAt nabla p η y) := by
  rw [D.inner_shapeOperatorAt nabla hLC.2 hη hy x,
    D.secondFundScalarAt_symm nabla hLC.1 η hx hy,
    ← D.inner_shapeOperatorAt nabla hLC.2 hη hx y, g.metricInner_comm]

/-! ### do Carmo Prop. 2.3: `S_η(x) = −(∇̄_x N)ᵀ` for any normal extension -/

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 6, Prop. 2.3: let `p ∈ M`, `x ∈ T_pM̄` and
`η ∈ (T_pM)^⊥`, and let `N` be *any* local extension of `η` normal to `M`.
Then `S_η(x) = −(∇̄_x N)ᵀ` — i.e. the shape operator at `p` is computed by any
normal extension of `η` and any extension of `x`, independently of the
choices. -/
theorem shapeOperatorAt_eq_shapeOperator (hcompat : nabla.IsMetricCompatible g)
    {p : M} {η : TangentSpace I p} (hη : η ∈ D.normalSpace p)
    {N : SmoothVectorField I M} (hN : D.IsNormalField N) (hNp : N p = η)
    (X : SmoothVectorField I M) :
    D.shapeOperatorAt nabla p η (X p) = D.shapeOperator nabla N X p := by
  refine D.eq_of_inner_eq_of_mem_tang (D.shapeOperatorAt_mem nabla p η (X p))
    (D.shapeOperator_mem nabla N X p) fun w hw => ?_
  -- pair both sides against `w ∈ T_pM` through the Weingarten pairing
  rw [D.inner_shapeOperatorAt nabla hcompat hη hw (X p)]
  have hw' : w = D.tangentExtension p w p := (D.tangentExtension_apply_self hw).symm
  conv_rhs => rw [hw']
  rw [D.inner_shapeOperator_apply nabla hcompat X
    (D.isTangentField_tangentExtension p w) hN p]
  -- both sides are `⟨B(x, w), η⟩`
  rw [hNp]
  simp only [secondFundScalarAt]
  congr 1
  have hb := D.secondFundFormAt_apply_apply nabla
    (D.isTangentField_tangentExtension p w) X p
  rw [D.tangentExtension_apply_self hw] at hb
  exact hb

end DCImmersedPatch

end Riemannian
