import DoCarmoLib.Riemannian.Manifold.DoCarmoCh4

/-!
# do Carmo Chapter 6 interface — isometric immersions, the second fundamental form

Faithful Lean interface for do Carmo's Chapter 6 (§2 The second fundamental
form). do Carmo works, for an immersion `f : Mⁿ → M̄ⁿ⁺ᵐ`, on a neighbourhood
`U ⊆ M` identified with `f(U) ⊆ M̄`, identifying each `v ∈ T_qM` with
`df_q(v) ∈ T_{f(q)}M̄`. After this identification the entire chapter takes place
*inside the ambient manifold*: what remains of the immersion is

* the family of tangent subspaces `T_pM ⊆ T_pM̄` — a distribution `tang` of
  constant rank `n` on the ambient manifold;
* the orthogonal splitting `T_pM̄ = T_pM ⊕ (T_pM)^⊥`, `v = vᵀ + vᴺ`, varying
  differentiably with `p` — captured by requiring the pointwise `g`-orthogonal
  projection onto `tang` to preserve smoothness of vector fields;
* closure of the tangent fields under the Lie bracket (`[X̄, Ȳ] = [X, Y]` on
  `M`, do Carmo's identification of brackets of extensions).

The structure `DCImmersedPatch` records exactly this data. Everything else is
*derived*: uniqueness and tensoriality of the projection, the induced
connection `∇_X Y = (∇̄_X Y)ᵀ`, and the second fundamental form
`B(X, Y) = ∇̄_X Y − ∇_X Y = (∇̄_X Y)ᴺ` with its bilinearity and symmetry
(`prop:dc-ch6-2-1`). In this formulation vector fields on `M` *are* their
extensions, so do Carmo's "`B(X,Y)` does not depend on the extensions" becomes
the well-definedness of `B` as an operator on ambient fields together with its
tensoriality.

The construction of a `DCImmersedPatch` from an actual isometric immersion
`f : M → M̄` (`DCSmoothImmersion`, do Carmo §0 Prop. 3.7 local normal form) is
the analytic bridge deferred to later work; the present file develops the
geometry of the identified picture, which is where all of Chapter 6 lives.

Reference: do Carmo, *Riemannian Geometry*, Ch. 6 §2.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** do Carmo Ch. 6 §2, the working setup: an **immersed patch** in the
ambient Riemannian manifold `(M̄, g)` — the picture obtained from an isometric
immersion `f : Mⁿ → M̄` after identifying a neighbourhood `U ⊆ M` with
`f(U) ⊆ M̄` and each tangent vector with its image under `df`. The data is the
distribution `p ↦ T_pM ⊆ T_pM̄` of constant rank `n`, together with the two
facts do Carmo's identification provides:

* the `g`-orthogonal splitting `T_pM̄ = T_pM ⊕ (T_pM)^⊥` is *differentiable*:
  the pointwise orthogonal projection of a smooth vector field onto the
  distribution is again a smooth vector field (`tangentProj`, characterized by
  `tangentProj_mem` and `inner_tangentProj_sub`);
* fields tangent to `M` are closed under the Lie bracket (`lieBracket_mem`) —
  on `M`, `[X̄, Ȳ] = [X, Y]`.

The projection is *determined* by the distribution (see `tangentProj_eq_at`);
carrying it as data records the differentiability of the splitting. -/
structure DCImmersedPatch (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : RiemannianMetric I M) where
  /-- The dimension `n` of the immersed manifold. -/
  dim : ℕ
  /-- The tangent distribution: at `p`, the subspace `T_pM ⊆ T_pM̄`. -/
  tang : ∀ p : M, Submodule ℝ (TangentSpace I p)
  /-- The distribution has constant rank `n = dim`. -/
  finrank_tang : ∀ p : M, Module.finrank ℝ (tang p) = dim
  /-- The tangential projection `X ↦ Xᵀ` on smooth vector fields. -/
  tangentProj : SmoothVectorField I M → SmoothVectorField I M
  /-- `Xᵀ(p)` lies in the distribution. -/
  tangentProj_mem : ∀ (X : SmoothVectorField I M) (p : M), tangentProj X p ∈ tang p
  /-- `X(p) − Xᵀ(p)` is `g`-orthogonal to the distribution: `tangentProj` is the
  pointwise orthogonal projection. -/
  inner_tangentProj_sub : ∀ (X : SmoothVectorField I M) (p : M),
    ∀ v ∈ tang p, g.metricInner p v (X p - tangentProj X p) = 0
  /-- Tangent fields are closed under the Lie bracket. -/
  lieBracket_mem : ∀ X Y : SmoothVectorField I M,
    (∀ p, X p ∈ tang p) → (∀ p, Y p ∈ tang p) →
    ∀ p, DCLieBracket X Y p ∈ tang p

namespace DCImmersedPatch

variable {g : RiemannianMetric I M} (D : DCImmersedPatch I M g)

/-! ### The normal space and the orthogonal splitting -/

/-- **Math.** do Carmo Ch. 6 §2: the **normal space** `(T_pM)^⊥` at `p` — the
`g`-orthogonal complement of the tangent distribution in `T_pM̄`. -/
def normalSpace (p : M) : Submodule ℝ (TangentSpace I p) where
  carrier := {v | ∀ w ∈ D.tang p, g.metricInner p w v = 0}
  add_mem' := by
    intro a b ha hb w hw
    rw [g.metricInner_add_right, ha w hw, hb w hw, add_zero]
  zero_mem' := by
    intro w hw
    exact g.metricInner_zero_right p w
  smul_mem' := by
    intro c v hv w hw
    rw [g.metricInner_smul_right, hv w hw, mul_zero]

omit [CompleteSpace E] in
@[simp] theorem mem_normalSpace_iff {p : M} {v : TangentSpace I p} :
    v ∈ D.normalSpace p ↔ ∀ w ∈ D.tang p, g.metricInner p w v = 0 :=
  Iff.rfl

omit [CompleteSpace E] in
/-- **Math.** A vector both tangent and normal at `p` is zero: the splitting
`T_pM̄ = T_pM ⊕ (T_pM)^⊥` is direct, by positive-definiteness of `g`. -/
theorem eq_zero_of_mem_tang_of_mem_normalSpace {p : M} {v : TangentSpace I p}
    (hv : v ∈ D.tang p) (hv' : v ∈ D.normalSpace p) : v = 0 := by
  by_contra h
  have hpos := g.metricInner_self_pos p v h
  rw [hv' v hv] at hpos
  exact lt_irrefl 0 hpos

omit [CompleteSpace E] in
/-- **Math.** Tangent–normal orthogonality: `⟨v, w⟩ = 0` for `v` tangent, `w`
normal at `p`. -/
theorem inner_eq_zero_of_mem_tang_of_mem_normalSpace {p : M}
    {v w : TangentSpace I p} (hv : v ∈ D.tang p) (hw : w ∈ D.normalSpace p) :
    g.metricInner p v w = 0 :=
  hw v hv

omit [CompleteSpace E] in
/-- **Math.** Normal–tangent orthogonality: `⟨w, v⟩ = 0` for `w` normal, `v`
tangent at `p`. -/
theorem inner_eq_zero_of_mem_normalSpace_of_mem_tang {p : M}
    {w v : TangentSpace I p} (hw : w ∈ D.normalSpace p) (hv : v ∈ D.tang p) :
    g.metricInner p w v = 0 := by
  rw [g.metricInner_comm]
  exact hw v hv

/-! ### The tangential projection: uniqueness and algebra

The pointwise orthogonal projection onto a subspace is unique; hence
`tangentProj` is pointwise determined by the distribution, and its algebraic
laws (additivity, `𝒟(M̄)`-homogeneity, behaviour on tangent and on normal
fields) all follow from the characterization. -/

omit [CompleteSpace E] in
/-- **Math.** **Uniqueness of the orthogonal projection.** If `u ∈ T_pM` and
`X(p) − u ⊥ T_pM`, then `u = Xᵀ(p)`. -/
theorem tangentProj_eq_at (X : SmoothVectorField I M) {p : M}
    {u : TangentSpace I p} (hu : u ∈ D.tang p)
    (horth : ∀ v ∈ D.tang p, g.metricInner p v (X p - u) = 0) :
    D.tangentProj X p = u := by
  have hd : D.tangentProj X p - u ∈ D.tang p :=
    sub_mem (D.tangentProj_mem X p) hu
  have hn : D.tangentProj X p - u ∈ D.normalSpace p := by
    rw [mem_normalSpace_iff]
    intro w hw
    have h : g.metricInner p w (X p - u)
        - g.metricInner p w (X p - D.tangentProj X p) = 0 := by
      rw [horth w hw, D.inner_tangentProj_sub X p w hw, sub_zero]
    rw [← g.metricInner_sub_right] at h
    have hv : (X p - u) - (X p - D.tangentProj X p)
        = D.tangentProj X p - u := by module
    rwa [hv] at h
  have h0 := D.eq_zero_of_mem_tang_of_mem_normalSpace hd hn
  exact sub_eq_zero.mp h0

omit [CompleteSpace E] in
/-- **Math.** The projection is **pointwise determined**: fields agreeing at `p`
have equal tangential projections at `p`. -/
theorem tangentProj_congr_apply {X Y : SmoothVectorField I M} {p : M}
    (h : X p = Y p) : D.tangentProj X p = D.tangentProj Y p :=
  D.tangentProj_eq_at X (D.tangentProj_mem Y p) fun v hv => by
    rw [h]; exact D.inner_tangentProj_sub Y p v hv

omit [CompleteSpace E] in
/-- **Math.** The projection fixes vectors already tangent: `X(p) ∈ T_pM ⟹
Xᵀ(p) = X(p)`. -/
theorem tangentProj_apply_of_mem {X : SmoothVectorField I M} {p : M}
    (h : X p ∈ D.tang p) : D.tangentProj X p = X p :=
  D.tangentProj_eq_at X h fun v hv => by
    rw [sub_self]
    exact g.metricInner_zero_right p v

omit [CompleteSpace E] in
/-- **Math.** The projection kills normal vectors: `X(p) ∈ (T_pM)^⊥ ⟹
Xᵀ(p) = 0`. -/
theorem tangentProj_apply_of_mem_normalSpace {X : SmoothVectorField I M} {p : M}
    (h : X p ∈ D.normalSpace p) : D.tangentProj X p = 0 :=
  D.tangentProj_eq_at X (zero_mem _) fun v hv => by
    rw [sub_zero]
    exact h v hv

omit [CompleteSpace E] in
/-- **Math.** Additivity of the tangential projection: `(X + Y)ᵀ = Xᵀ + Yᵀ`. -/
theorem tangentProj_add (X Y : SmoothVectorField I M) :
    D.tangentProj (X + Y) = D.tangentProj X + D.tangentProj Y := by
  ext p
  have hmem : (D.tangentProj X + D.tangentProj Y) p ∈ D.tang p := by
    rw [SmoothVectorField.add_apply]
    exact add_mem (D.tangentProj_mem X p) (D.tangentProj_mem Y p)
  refine D.tangentProj_eq_at (X + Y) hmem fun v hv => ?_
  rw [SmoothVectorField.add_apply, SmoothVectorField.add_apply]
  have hv2 : X p + Y p - (D.tangentProj X p + D.tangentProj Y p)
      = (X p - D.tangentProj X p) + (Y p - D.tangentProj Y p) := by module
  rw [hv2, g.metricInner_add_right, D.inner_tangentProj_sub X p v hv,
    D.inner_tangentProj_sub Y p v hv, add_zero]

omit [CompleteSpace E] in
/-- **Math.** `𝒟(M̄)`-homogeneity of the tangential projection:
`(fX)ᵀ = f Xᵀ` for a smooth scalar `f`. -/
theorem tangentProj_smul {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : SmoothVectorField I M) :
    D.tangentProj (SmoothVectorField.smul f hf X)
      = SmoothVectorField.smul f hf (D.tangentProj X) := by
  ext p
  have hmem : (SmoothVectorField.smul f hf (D.tangentProj X)) p ∈ D.tang p := by
    rw [SmoothVectorField.smul_apply]
    exact Submodule.smul_mem _ _ (D.tangentProj_mem X p)
  refine D.tangentProj_eq_at _ hmem fun v hv => ?_
  rw [SmoothVectorField.smul_apply, SmoothVectorField.smul_apply]
  have hv2 : f p • X p - f p • D.tangentProj X p
      = f p • (X p - D.tangentProj X p) := by module
  rw [hv2, g.metricInner_smul_right, D.inner_tangentProj_sub X p v hv, mul_zero]

omit [CompleteSpace E] in
/-- **Math.** `ℝ`-homogeneity of the tangential projection: `(cX)ᵀ = c Xᵀ`. -/
theorem tangentProj_constSMul (c : ℝ) (X : SmoothVectorField I M) :
    D.tangentProj (c • X) = c • D.tangentProj X := by
  ext p
  have hmem : (c • D.tangentProj X) p ∈ D.tang p := by
    rw [SmoothVectorField.constSMul_apply]
    exact Submodule.smul_mem _ _ (D.tangentProj_mem X p)
  refine D.tangentProj_eq_at _ hmem fun v hv => ?_
  rw [SmoothVectorField.constSMul_apply, SmoothVectorField.constSMul_apply]
  have hv2 : c • X p - c • D.tangentProj X p
      = c • (X p - D.tangentProj X p) := by module
  rw [hv2, g.metricInner_smul_right, D.inner_tangentProj_sub X p v hv, mul_zero]

omit [CompleteSpace E] in
/-- **Math.** `0ᵀ = 0`. -/
theorem tangentProj_zero : D.tangentProj 0 = 0 := by
  ext p
  refine D.tangentProj_eq_at _ (zero_mem _) fun v hv => ?_
  rw [SmoothVectorField.zero_apply, sub_zero]
  exact g.metricInner_zero_right p v

omit [CompleteSpace E] in
/-- **Math.** `(−X)ᵀ = −Xᵀ`. -/
theorem tangentProj_neg (X : SmoothVectorField I M) :
    D.tangentProj (-X) = -D.tangentProj X := by
  ext p
  have hmem : (-D.tangentProj X) p ∈ D.tang p := by
    rw [SmoothVectorField.neg_apply]
    exact neg_mem (D.tangentProj_mem X p)
  refine D.tangentProj_eq_at _ hmem fun v hv => ?_
  rw [SmoothVectorField.neg_apply, SmoothVectorField.neg_apply]
  have hv2 : -X p - -D.tangentProj X p = -(X p - D.tangentProj X p) := by module
  rw [hv2, g.metricInner_neg_right, D.inner_tangentProj_sub X p v hv, neg_zero]

omit [CompleteSpace E] in
/-- **Math.** `(X − Y)ᵀ = Xᵀ − Yᵀ`. -/
theorem tangentProj_sub (X Y : SmoothVectorField I M) :
    D.tangentProj (X - Y) = D.tangentProj X - D.tangentProj Y := by
  ext p
  have hmem : (D.tangentProj X - D.tangentProj Y) p ∈ D.tang p := by
    rw [SmoothVectorField.sub_apply]
    exact sub_mem (D.tangentProj_mem X p) (D.tangentProj_mem Y p)
  refine D.tangentProj_eq_at _ hmem fun v hv => ?_
  rw [SmoothVectorField.sub_apply, SmoothVectorField.sub_apply]
  have hv2 : X p - Y p - (D.tangentProj X p - D.tangentProj Y p)
      = (X p - D.tangentProj X p) - (Y p - D.tangentProj Y p) := by module
  rw [hv2, g.metricInner_sub_right, D.inner_tangentProj_sub X p v hv,
    D.inner_tangentProj_sub Y p v hv, sub_zero]

omit [CompleteSpace E] in
/-- **Math.** Idempotence: `(Xᵀ)ᵀ = Xᵀ`. -/
theorem tangentProj_tangentProj (X : SmoothVectorField I M) :
    D.tangentProj (D.tangentProj X) = D.tangentProj X := by
  ext p
  exact D.tangentProj_apply_of_mem (D.tangentProj_mem X p)

/-! ### Tangent fields, normal fields, and the normal projection -/

/-- **Math.** A field on the ambient manifold is a **tangent field** (of the
patch) when its value at each point lies in the tangent distribution — after
do Carmo's identification, these are exactly the local vector fields
`X ∈ 𝒳(U)` on the immersed manifold. -/
def IsTangentField (X : SmoothVectorField I M) : Prop :=
  ∀ p, X p ∈ D.tang p

/-- **Math.** A field is a **normal field** (`X ∈ 𝒳(U)^⊥`) when its value at
each point is `g`-orthogonal to the tangent distribution. -/
def IsNormalField (X : SmoothVectorField I M) : Prop :=
  ∀ p, X p ∈ D.normalSpace p

/-- **Math.** The **normal projection** `X ↦ Xᴺ = X − Xᵀ`. -/
def normalProj (X : SmoothVectorField I M) : SmoothVectorField I M :=
  X - D.tangentProj X

omit [CompleteSpace E] in
@[simp] theorem normalProj_apply (X : SmoothVectorField I M) (p : M) :
    D.normalProj X p = X p - D.tangentProj X p := by
  simp [normalProj]

omit [CompleteSpace E] in
/-- **Math.** `Xᴺ(p)` is normal at `p`. -/
theorem normalProj_mem (X : SmoothVectorField I M) (p : M) :
    D.normalProj X p ∈ D.normalSpace p := by
  rw [normalProj_apply, mem_normalSpace_iff]
  intro w hw
  exact D.inner_tangentProj_sub X p w hw

omit [CompleteSpace E] in
/-- **Math.** The splitting of a field into tangential and normal parts:
`X = Xᵀ + Xᴺ`. -/
theorem tangentProj_add_normalProj (X : SmoothVectorField I M) :
    D.tangentProj X + D.normalProj X = X := by
  ext p
  rw [SmoothVectorField.add_apply, normalProj_apply]
  module

omit [CompleteSpace E] in
/-- **Math.** Additivity of the normal projection: `(X + Y)ᴺ = Xᴺ + Yᴺ`. -/
theorem normalProj_add (X Y : SmoothVectorField I M) :
    D.normalProj (X + Y) = D.normalProj X + D.normalProj Y := by
  ext p
  simp only [normalProj_apply, SmoothVectorField.add_apply, D.tangentProj_add]
  module

omit [CompleteSpace E] in
/-- **Math.** `(X − Y)ᴺ = Xᴺ − Yᴺ`. -/
theorem normalProj_sub (X Y : SmoothVectorField I M) :
    D.normalProj (X - Y) = D.normalProj X - D.normalProj Y := by
  ext p
  simp only [normalProj_apply, SmoothVectorField.sub_apply, D.tangentProj_sub]
  module

omit [CompleteSpace E] in
/-- **Math.** `𝒟(M̄)`-homogeneity of the normal projection: `(fX)ᴺ = f Xᴺ`. -/
theorem normalProj_smul {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : SmoothVectorField I M) :
    D.normalProj (SmoothVectorField.smul f hf X)
      = SmoothVectorField.smul f hf (D.normalProj X) := by
  ext p
  simp only [normalProj_apply, SmoothVectorField.smul_apply, D.tangentProj_smul]
  module

omit [CompleteSpace E] in
theorem isTangentField_tangentProj (X : SmoothVectorField I M) :
    D.IsTangentField (D.tangentProj X) :=
  D.tangentProj_mem X

omit [CompleteSpace E] in
theorem isNormalField_normalProj (X : SmoothVectorField I M) :
    D.IsNormalField (D.normalProj X) :=
  D.normalProj_mem X

omit [CompleteSpace E] in
/-- **Math.** On tangent fields the tangential projection is the identity. -/
theorem IsTangentField.tangentProj_eq {D : DCImmersedPatch I M g}
    {X : SmoothVectorField I M} (hX : D.IsTangentField X) :
    D.tangentProj X = X := by
  ext p
  exact D.tangentProj_apply_of_mem (hX p)

omit [CompleteSpace E] in
/-- **Math.** Tangent fields have no normal part. -/
theorem IsTangentField.normalProj_eq_zero {D : DCImmersedPatch I M g}
    {X : SmoothVectorField I M} (hX : D.IsTangentField X) :
    D.normalProj X = 0 := by
  ext p
  rw [normalProj_apply, D.tangentProj_apply_of_mem (hX p),
    SmoothVectorField.zero_apply, sub_self]

omit [CompleteSpace E] in
/-- **Math.** Normal fields have no tangential part. -/
theorem IsNormalField.tangentProj_eq_zero {D : DCImmersedPatch I M g}
    {X : SmoothVectorField I M} (hX : D.IsNormalField X) :
    D.tangentProj X = 0 := by
  ext p
  rw [D.tangentProj_apply_of_mem_normalSpace (hX p), SmoothVectorField.zero_apply]

omit [CompleteSpace E] in
/-- **Math.** On normal fields the normal projection is the identity. -/
theorem IsNormalField.normalProj_eq {D : DCImmersedPatch I M g}
    {X : SmoothVectorField I M} (hX : D.IsNormalField X) :
    D.normalProj X = X := by
  ext p
  rw [normalProj_apply, D.tangentProj_apply_of_mem_normalSpace (hX p), sub_zero]

/-- **Math.** The Lie bracket of tangent fields is tangent (`[X̄, Ȳ] = [X, Y]`
on `M`), at the level of the bundled bracket field. -/
theorem isTangentField_bracketField {X Y : SmoothVectorField I M}
    (hX : D.IsTangentField X) (hY : D.IsTangentField Y) :
    D.IsTangentField (bracketField X Y) := fun p =>
  D.lieBracket_mem X Y hX hY p

/-! ### The induced connection `∇_X Y = (∇̄_X Y)ᵀ`

do Carmo Ch. 6 §2 (display before Prop. 2.1): for fields `X, Y` tangent to the
patch, the tangential part of the ambient covariant derivative is the
Levi-Civita connection of the induced metric (cf. do Carmo Ch. 2, Exercise 3).
Here we define the operator on all ambient fields and prove the connection
laws, symmetry and metric compatibility *restricted to tangent fields*. -/

variable (nabla : AffineConnection I M)

/-- **Math.** The **induced connection** of the patch:
`∇_X Y = (∇̄_X Y)ᵀ`, the tangential part of the ambient covariant
derivative. -/
def inducedCov (X Y : SmoothVectorField I M) : SmoothVectorField I M :=
  D.tangentProj (nabla.cov X Y)

omit [CompleteSpace E] in
theorem isTangentField_inducedCov (X Y : SmoothVectorField I M) :
    D.IsTangentField (D.inducedCov nabla X Y) :=
  D.tangentProj_mem _

omit [CompleteSpace E] in
/-- **Math.** Additivity of `∇` in the direction slot. -/
theorem inducedCov_add_left (X Y Z : SmoothVectorField I M) :
    D.inducedCov nabla (X + Y) Z
      = D.inducedCov nabla X Z + D.inducedCov nabla Y Z := by
  simp only [inducedCov, nabla.add_left, D.tangentProj_add]

omit [CompleteSpace E] in
/-- **Math.** `𝒟`-homogeneity of `∇` in the direction slot: `∇_{fX} Z = f ∇_X Z`. -/
theorem inducedCov_smul_left {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Z : SmoothVectorField I M) :
    D.inducedCov nabla (SmoothVectorField.smul f hf X) Z
      = SmoothVectorField.smul f hf (D.inducedCov nabla X Z) := by
  simp only [inducedCov, nabla.smul_left, D.tangentProj_smul]

omit [CompleteSpace E] in
/-- **Math.** Additivity of `∇` in the derived slot. -/
theorem inducedCov_add_right (X Y Z : SmoothVectorField I M) :
    D.inducedCov nabla X (Y + Z)
      = D.inducedCov nabla X Y + D.inducedCov nabla X Z := by
  simp only [inducedCov, nabla.add_right, D.tangentProj_add]

omit [CompleteSpace E] in
/-- **Math.** The Leibniz rule for the induced connection on a *tangent* field:
`∇_X (fY) = f ∇_X Y + X(f) Y`. (Tangency of `Y` is what keeps the first-order
term `X(f) Y` inside the tangent distribution.) -/
theorem inducedCov_smul_right {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : SmoothVectorField I M) {Y : SmoothVectorField I M}
    (hY : D.IsTangentField Y) :
    D.inducedCov nabla X (SmoothVectorField.smul f hf Y)
      = SmoothVectorField.smul f hf (D.inducedCov nabla X Y)
        + SmoothVectorField.smul (X.dir f) (X.dir_contMDiff hf) Y := by
  simp only [inducedCov]
  rw [nabla.cov_smul_right hf X Y, D.tangentProj_add, D.tangentProj_smul,
    D.tangentProj_smul, hY.tangentProj_eq]

/-- **Math.** **Symmetry of the induced connection**: for tangent fields,
`∇_X Y − ∇_Y X = [X, Y]`. Together with `inducedCov_compat` this identifies
`∇` as the Levi-Civita connection of the induced metric (do Carmo Ch. 2,
Exercise 3 / Thm. 3.6 uniqueness). -/
theorem inducedCov_sub_swap {X Y : SmoothVectorField I M}
    (hsym : nabla.IsSymmetric) (hX : D.IsTangentField X)
    (hY : D.IsTangentField Y) :
    D.inducedCov nabla X Y - D.inducedCov nabla Y X = bracketField X Y := by
  have hcov : nabla.cov X Y - nabla.cov Y X = bracketField X Y := by
    ext p
    simp only [SmoothVectorField.sub_apply, bracketField_apply]
    exact hsym X Y p
  calc D.inducedCov nabla X Y - D.inducedCov nabla Y X
      = D.tangentProj (nabla.cov X Y - nabla.cov Y X) :=
        (D.tangentProj_sub _ _).symm
    _ = D.tangentProj (bracketField X Y) := by rw [hcov]
    _ = bracketField X Y := (D.isTangentField_bracketField hX hY).tangentProj_eq

omit [CompleteSpace E] in
/-- **Math.** **Metric compatibility of the induced connection**: for tangent
fields `Y, Z`, `X⟨Y, Z⟩ = ⟨∇_X Y, Z⟩ + ⟨Y, ∇_X Z⟩` — the normal parts of the
ambient derivatives pair to zero against tangent fields. -/
theorem inducedCov_compat (hcompat : nabla.IsMetricCompatible g)
    (X : SmoothVectorField I M) {Y Z : SmoothVectorField I M}
    (hY : D.IsTangentField Y) (hZ : D.IsTangentField Z) (p : M) :
    X.dir (fun q => g.metricInner q (Y q) (Z q)) p
      = g.metricInner p (D.inducedCov nabla X Y p) (Z p)
        + g.metricInner p (Y p) (D.inducedCov nabla X Z p) := by
  rw [hcompat X Y Z p]
  have hsplit : ∀ W : SmoothVectorField I M,
      W p = D.tangentProj W p + D.normalProj W p := fun W => by
    rw [normalProj_apply]; module
  congr 1
  · rw [hsplit (nabla.cov X Y), g.metricInner_add_left,
      D.inner_eq_zero_of_mem_normalSpace_of_mem_tang
        (D.normalProj_mem _ p) (hZ p), add_zero]
    rfl
  · rw [hsplit (nabla.cov X Z), g.metricInner_add_right,
      D.inner_eq_zero_of_mem_tang_of_mem_normalSpace
        (hY p) (D.normalProj_mem _ p), add_zero]
    rfl

/-! ### The second fundamental form `B` (do Carmo Ch. 6, Prop. 2.1) -/

/-- **Math.** do Carmo Ch. 6 §2: the **second fundamental form** of the patch,
`B(X, Y) = ∇̄_X Y − ∇_X Y = (∇̄_X Y)ᴺ`, a normal-valued form on fields. In the
identified picture fields are their own extensions, so well-definedness (do
Carmo's "does not depend on the extensions") is built in, and dependence only
on pointwise values follows from bilinearity (see `prop:dc-ch6-2-1`). -/
def secondFundForm (X Y : SmoothVectorField I M) : SmoothVectorField I M :=
  D.normalProj (nabla.cov X Y)

omit [CompleteSpace E] in
/-- **Math.** The **Gauss decomposition** `∇̄_X Y = ∇_X Y + B(X, Y)` of the
ambient covariant derivative into tangential and normal parts. -/
theorem cov_eq_inducedCov_add_secondFundForm (X Y : SmoothVectorField I M) :
    nabla.cov X Y = D.inducedCov nabla X Y + D.secondFundForm nabla X Y :=
  (D.tangentProj_add_normalProj (nabla.cov X Y)).symm

omit [CompleteSpace E] in
/-- **Math.** `B` takes values in the normal spaces:
`B(X, Y)(p) ∈ (T_pM)^⊥`. -/
theorem secondFundForm_mem (X Y : SmoothVectorField I M) (p : M) :
    D.secondFundForm nabla X Y p ∈ D.normalSpace p :=
  D.normalProj_mem _ p

omit [CompleteSpace E] in
theorem isNormalField_secondFundForm (X Y : SmoothVectorField I M) :
    D.IsNormalField (D.secondFundForm nabla X Y) :=
  D.secondFundForm_mem nabla X Y

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 6, Prop. 2.1 (additivity in `X`):
`B(X₁ + X₂, Y) = B(X₁, Y) + B(X₂, Y)`. -/
theorem secondFundForm_add_left (X₁ X₂ Y : SmoothVectorField I M) :
    D.secondFundForm nabla (X₁ + X₂) Y
      = D.secondFundForm nabla X₁ Y + D.secondFundForm nabla X₂ Y := by
  simp only [secondFundForm, normalProj, nabla.add_left, D.tangentProj_add]
  ext p
  simp only [SmoothVectorField.sub_apply, SmoothVectorField.add_apply]
  module

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 6, Prop. 2.1 (additivity in `Y`):
`B(X, Y₁ + Y₂) = B(X, Y₁) + B(X, Y₂)`. -/
theorem secondFundForm_add_right (X Y₁ Y₂ : SmoothVectorField I M) :
    D.secondFundForm nabla X (Y₁ + Y₂)
      = D.secondFundForm nabla X Y₁ + D.secondFundForm nabla X Y₂ := by
  simp only [secondFundForm, normalProj, nabla.add_right, D.tangentProj_add]
  ext p
  simp only [SmoothVectorField.sub_apply, SmoothVectorField.add_apply]
  module

omit [CompleteSpace E] in
/-- **Math.** `B(X₁ − X₂, Y) = B(X₁, Y) − B(X₂, Y)`, from additivity. -/
theorem secondFundForm_sub_left (X₁ X₂ Y : SmoothVectorField I M) :
    D.secondFundForm nabla (X₁ - X₂) Y
      = D.secondFundForm nabla X₁ Y - D.secondFundForm nabla X₂ Y := by
  have hcov : nabla.cov (X₁ - X₂) Y = nabla.cov X₁ Y - nabla.cov X₂ Y := by
    ext q
    rw [SmoothVectorField.sub_apply]
    exact nabla.cov_sub_left X₁ X₂ Y q
  simp only [secondFundForm, hcov, D.normalProj_sub]

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 6, Prop. 2.1 (`𝒟(U)`-homogeneity in `X`):
`B(fX, Y) = f B(X, Y)`. -/
theorem secondFundForm_smul_left {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y : SmoothVectorField I M) :
    D.secondFundForm nabla (SmoothVectorField.smul f hf X) Y
      = SmoothVectorField.smul f hf (D.secondFundForm nabla X Y) := by
  simp only [secondFundForm, normalProj, nabla.smul_left, D.tangentProj_smul]
  ext p
  simp only [SmoothVectorField.sub_apply, SmoothVectorField.smul_apply]
  module

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 6, Prop. 2.1 (`𝒟(U)`-homogeneity in `Y`):
`B(X, fY) = f B(X, Y)` for `Y` a *tangent* field. This is do Carmo's
computation `B(X, fY) = f̄ ∇̄_X Ȳ − f ∇_X Y + X̄(f̄) Ȳ − X(f) Y`, where the two
first-order terms cancel because `Y` is tangent (`f = f̄`, `Y = Ȳ` on `M`). -/
theorem secondFundForm_smul_right {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : SmoothVectorField I M) {Y : SmoothVectorField I M}
    (hY : D.IsTangentField Y) :
    D.secondFundForm nabla X (SmoothVectorField.smul f hf Y)
      = SmoothVectorField.smul f hf (D.secondFundForm nabla X Y) := by
  simp only [secondFundForm, normalProj]
  rw [nabla.cov_smul_right hf X Y, D.tangentProj_add, D.tangentProj_smul,
    D.tangentProj_smul, hY.tangentProj_eq]
  ext p
  simp only [SmoothVectorField.sub_apply, SmoothVectorField.add_apply,
    SmoothVectorField.smul_apply]
  module

/-- **Math.** do Carmo Ch. 6, Prop. 2.1 (**symmetry**): `B(X, Y) = B(Y, X)` for
tangent fields, by symmetry of the ambient Riemannian connection and
tangency of the bracket:
`B(X,Y) − B(Y,X) = (∇̄_X Y − ∇̄_Y X)ᴺ = [X, Y]ᴺ = 0`. -/
theorem secondFundForm_symm {X Y : SmoothVectorField I M}
    (hsym : nabla.IsSymmetric) (hX : D.IsTangentField X)
    (hY : D.IsTangentField Y) :
    D.secondFundForm nabla X Y = D.secondFundForm nabla Y X := by
  have hcov : nabla.cov X Y - nabla.cov Y X = bracketField X Y := by
    ext p
    simp only [SmoothVectorField.sub_apply, bracketField_apply]
    exact hsym X Y p
  have htp : D.tangentProj (nabla.cov X Y) - D.tangentProj (nabla.cov Y X)
      = bracketField X Y := by
    rw [← D.tangentProj_sub, hcov,
      (D.isTangentField_bracketField hX hY).tangentProj_eq]
  ext p
  have h1 := congrArg (fun F : SmoothVectorField I M => F p) hcov
  have h2 := congrArg (fun F : SmoothVectorField I M => F p) htp
  simp only [SmoothVectorField.sub_apply] at h1 h2
  simp only [secondFundForm, normalProj_apply]
  linear_combination (norm := module) h1 - h2

end DCImmersedPatch

end Riemannian
