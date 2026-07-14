import OpenGALib.Riemannian.Connection.ChartCurvature
import OpenGALib.Riemannian.Manifold.DoCarmoCh4Sectional
import OpenGALib.Riemannian.Manifold.DoCarmoCh4Tensor

/-!
# The pointwise curvature tensor (do Carmo Ch. 4, Prop. 2.2 / Rem. 2.3, read pointwise)

do Carmo's curvature operator `R(X,Y)Z = ∇_Y∇_X Z − ∇_X∇_Y Z + ∇_{[X,Y]}Z` is a
**tensor**: although it is built from covariant derivatives, its value at a point
`p` depends only on the values `X(p), Y(p), Z(p)` (`curvature_apply_congr`). This
is the pointwise reading of the `𝒟(M)`-multilinearity established in Ch. 4
(`curvature_add_*`, `curvature_smul_*`).

From it we build the **pointwise curvature operator**
`curvatureOperatorAt nabla p : T_pM³ → T_pM` (the value of `R(X,Y)Z` at `p` for
any smooth extensions of the given tangent vectors) and its `(0,4)` avatar
`curvatureFormAt g nabla p : T_pM⁴ → ℝ`, `⟨R(x,y)z, t⟩_g`. For the Levi-Civita
connection the latter is an **algebraic curvature form** on `T_pM`
(`isAlgCurvatureForm_curvatureFormAt`), the bridge from the field-level symmetries
of Prop. 2.5 to the pointwise linear algebra of Ch. 4 §3 (sectional curvature,
`eq_kronecker_iff_const`) used for the constant-curvature computations of Ch. 8.

## Method

A smooth field vanishing at `p` decomposes as `∑ᵢ fᵢ • Wᵢ + τ` with `fᵢ(p) = 0`
and `τ` vanishing near `p` (`exists_decomposition_of_apply_eq_zero`). Homogeneity
of `R` in a slot kills each `fᵢ • Wᵢ` summand (`fᵢ(p) = 0`), and the same
homogeneity kills the `τ` remainder (`τ = f·τ` with `f(p) = 0`); so `R` against a
field vanishing at `p` vanishes at `p`, slot by slot.

Reference: do Carmo, *Riemannian Geometry*, Ch. 4 §2.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian

namespace AffineConnection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]
  (nabla : AffineConnection I M)

/-! ## The curvature against the zero field -/

/-- **Math.** `R(0, Y)Z = 0` at `p`: the curvature vanishes against the zero direction field. -/
theorem curvature_zero_left (Y Z : SmoothVectorField I M) (p : M) :
    (nabla.curvature 0 Y Z) p = 0 := by
  have h := nabla.curvature_add_left 0 0 Y Z p
  have e : (0 : SmoothVectorField I M) + 0 = 0 := by ext q; simp
  rw [e] at h
  linear_combination (norm := module) -h

/-- **Math.** `R(X, Y)0 = 0` at `p`: the curvature vanishes against the zero field. -/
theorem curvature_zero_right (X Y : SmoothVectorField I M) (p : M) :
    (nabla.curvature X Y 0) p = 0 := by
  have h := nabla.curvature_add_right X Y 0 0 p
  have e : (0 : SmoothVectorField I M) + 0 = 0 := by ext q; simp
  rw [e] at h
  linear_combination (norm := module) -h

/-! ## Vanishing of `R` against a field vanishing at `p`, slot by slot -/

/-- **Math.** **Direction slot, remainder:** if `τ =ᶠ 0` near `p` then `R(τ,Y)Z|_p = 0`. -/
theorem curvature_apply_eq_zero_of_eventuallyEq_zero_left {τ : SmoothVectorField I M}
    (Y Z : SmoothVectorField I M) {p : M} (hτ : ∀ᶠ q in nhds p, τ q = 0) :
    nabla.curvature τ Y Z p = 0 := by
  obtain ⟨f, hf, hfp, hfτ⟩ := exists_smul_eq_self_of_eventuallyEq_zero hτ
  have h := nabla.curvature_smul_left hf τ Y Z p
  rw [hfτ, hfp, zero_smul] at h
  exact h

/-- **Math.** **Last slot, remainder:** if `τ =ᶠ 0` near `p` then `R(X,Y)τ|_p = 0`. -/
theorem curvature_apply_eq_zero_of_eventuallyEq_zero_right {τ : SmoothVectorField I M}
    (X Y : SmoothVectorField I M) {p : M} (hτ : ∀ᶠ q in nhds p, τ q = 0) :
    nabla.curvature X Y τ p = 0 := by
  obtain ⟨f, hf, hfp, hfτ⟩ := exists_smul_eq_self_of_eventuallyEq_zero hτ
  have h := nabla.curvature_smul_right hf X Y τ p
  rw [hfτ, hfp, zero_smul] at h
  exact h

/-- **Math.** **Direction slot, finite sum:** `R` annihilates, at `p`, direction fields that
are pointwise finite sums `Σᵢ fᵢ Wᵢ` with all scalars vanishing at `p`. -/
theorem curvature_apply_eq_zero_of_forall_eq_sum_left {ι : Type*} (s : Finset ι)
    {f : ι → M → ℝ} (hf : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f i))
    (W : ι → SmoothVectorField I M) (Y Z : SmoothVectorField I M) {p : M}
    (hfp : ∀ i ∈ s, f i p = 0) {σ : SmoothVectorField I M}
    (hσ : ∀ q, σ q = ∑ i ∈ s, f i q • W i q) :
    nabla.curvature σ Y Z p = 0 := by
  classical
  induction s using Finset.induction_on generalizing σ with
  | empty =>
    have hσ0 : σ = 0 := SmoothVectorField.ext fun q => by simpa using hσ q
    rw [hσ0]; exact nabla.curvature_zero_left Y Z p
  | @insert a s ha ih =>
    have key : ∀ q, (σ - SmoothVectorField.smul (f a) (hf a) (W a)) q
        = ∑ i ∈ s, f i q • W i q := by
      intro q
      rw [SmoothVectorField.sub_apply, SmoothVectorField.smul_apply, hσ q,
        Finset.sum_insert ha]
      abel
    have hzero := ih (fun i hi => hfp i (Finset.mem_insert_of_mem hi)) key
    have hcancel : (σ - SmoothVectorField.smul (f a) (hf a) (W a))
        + SmoothVectorField.smul (f a) (hf a) (W a) = σ := by
      ext q; rw [SmoothVectorField.add_apply, SmoothVectorField.sub_apply]; abel
    have hsub := nabla.curvature_add_left
      (σ - SmoothVectorField.smul (f a) (hf a) (W a))
      (SmoothVectorField.smul (f a) (hf a) (W a)) Y Z p
    rw [hcancel] at hsub
    have hsm := nabla.curvature_smul_left (hf a) (W a) Y Z p
    rw [hsub, hzero, hsm, hfp a (Finset.mem_insert_self a s), zero_smul, zero_add]

/-- **Math.** **Last slot, finite sum:** `R` annihilates, at `p`, last-slot fields that are
pointwise finite sums `Σᵢ fᵢ Wᵢ` with all scalars vanishing at `p`. -/
theorem curvature_apply_eq_zero_of_forall_eq_sum_right {ι : Type*} (s : Finset ι)
    {f : ι → M → ℝ} (hf : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f i))
    (W : ι → SmoothVectorField I M) (X Y : SmoothVectorField I M) {p : M}
    (hfp : ∀ i ∈ s, f i p = 0) {σ : SmoothVectorField I M}
    (hσ : ∀ q, σ q = ∑ i ∈ s, f i q • W i q) :
    nabla.curvature X Y σ p = 0 := by
  classical
  induction s using Finset.induction_on generalizing σ with
  | empty =>
    have hσ0 : σ = 0 := SmoothVectorField.ext fun q => by simpa using hσ q
    rw [hσ0]; exact nabla.curvature_zero_right X Y p
  | @insert a s ha ih =>
    have key : ∀ q, (σ - SmoothVectorField.smul (f a) (hf a) (W a)) q
        = ∑ i ∈ s, f i q • W i q := by
      intro q
      rw [SmoothVectorField.sub_apply, SmoothVectorField.smul_apply, hσ q,
        Finset.sum_insert ha]
      abel
    have hzero := ih (fun i hi => hfp i (Finset.mem_insert_of_mem hi)) key
    have hcancel : (σ - SmoothVectorField.smul (f a) (hf a) (W a))
        + SmoothVectorField.smul (f a) (hf a) (W a) = σ := by
      ext q; rw [SmoothVectorField.add_apply, SmoothVectorField.sub_apply]; abel
    have hsub := nabla.curvature_add_right X Y
      (σ - SmoothVectorField.smul (f a) (hf a) (W a))
      (SmoothVectorField.smul (f a) (hf a) (W a)) p
    rw [hcancel] at hsub
    have hsm := nabla.curvature_smul_right (hf a) X Y (W a) p
    rw [hsub, hzero, hsm, hfp a (Finset.mem_insert_self a s), zero_smul, zero_add]

/-- **Math.** **Direction slot:** if `σ(p) = 0` then `R(σ,Y)Z|_p = 0`. -/
theorem curvature_apply_eq_zero_of_apply_eq_zero_left (Y Z : SmoothVectorField I M)
    {σ : SmoothVectorField I M} {p : M} (hσ : σ p = 0) :
    nabla.curvature σ Y Z p = 0 := by
  obtain ⟨k, f, hf, W, τ, hfp, hτ0, hdecomp⟩ :=
    exists_decomposition_of_apply_eq_zero σ hσ
  set S : SmoothVectorField I M := σ - τ with hSdef
  have hSsum : ∀ q, S q = ∑ i, f i q • W i q := by
    intro q; rw [hSdef, SmoothVectorField.sub_apply, hdecomp q]; abel
  have hστ : S + τ = σ := by
    ext q; rw [hSdef, SmoothVectorField.add_apply, SmoothVectorField.sub_apply]; abel
  have hadd := nabla.curvature_add_left S τ Y Z p
  rw [hστ] at hadd
  rw [hadd,
    nabla.curvature_apply_eq_zero_of_forall_eq_sum_left Finset.univ hf W Y Z
      (fun i _ => hfp i) hSsum,
    nabla.curvature_apply_eq_zero_of_eventuallyEq_zero_left Y Z hτ0, add_zero]

/-- **Math.** **Middle slot:** if `σ(p) = 0` then `R(X,σ)Z|_p = 0` (via antisymmetry). -/
theorem curvature_apply_eq_zero_of_apply_eq_zero_middle (X Z : SmoothVectorField I M)
    {σ : SmoothVectorField I M} {p : M} (hσ : σ p = 0) :
    nabla.curvature X σ Z p = 0 := by
  rw [nabla.curvature_antisymm_left X σ Z,
    nabla.curvature_apply_eq_zero_of_apply_eq_zero_left X Z hσ, neg_zero]

/-- **Math.** **Last slot:** if `σ(p) = 0` then `R(X,Y)σ|_p = 0`. -/
theorem curvature_apply_eq_zero_of_apply_eq_zero_right (X Y : SmoothVectorField I M)
    {σ : SmoothVectorField I M} {p : M} (hσ : σ p = 0) :
    nabla.curvature X Y σ p = 0 := by
  obtain ⟨k, f, hf, W, τ, hfp, hτ0, hdecomp⟩ :=
    exists_decomposition_of_apply_eq_zero σ hσ
  set S : SmoothVectorField I M := σ - τ with hSdef
  have hSsum : ∀ q, S q = ∑ i, f i q • W i q := by
    intro q; rw [hSdef, SmoothVectorField.sub_apply, hdecomp q]; abel
  have hστ : S + τ = σ := by
    ext q; rw [hSdef, SmoothVectorField.add_apply, SmoothVectorField.sub_apply]; abel
  have hadd := nabla.curvature_add_right X Y S τ p
  rw [hστ] at hadd
  rw [hadd,
    nabla.curvature_apply_eq_zero_of_forall_eq_sum_right Finset.univ hf W X Y
      (fun i _ => hfp i) hSsum,
    nabla.curvature_apply_eq_zero_of_eventuallyEq_zero_right X Y hτ0, add_zero]

/-! ## Subtraction versions of slot-additivity -/

theorem curvature_sub_left (X₁ X₂ Y Z : SmoothVectorField I M) (p : M) :
    (nabla.curvature (X₁ - X₂) Y Z) p
      = (nabla.curvature X₁ Y Z) p - (nabla.curvature X₂ Y Z) p := by
  have h := nabla.curvature_add_left (X₁ - X₂) X₂ Y Z p
  have e : (X₁ - X₂) + X₂ = X₁ := by ext q; simp
  rw [e] at h
  linear_combination (norm := module) -h

theorem curvature_sub_middle (X Y₁ Y₂ Z : SmoothVectorField I M) (p : M) :
    (nabla.curvature X (Y₁ - Y₂) Z) p
      = (nabla.curvature X Y₁ Z) p - (nabla.curvature X Y₂ Z) p := by
  have h := nabla.curvature_add_middle X (Y₁ - Y₂) Y₂ Z p
  have e : (Y₁ - Y₂) + Y₂ = Y₁ := by ext q; simp
  rw [e] at h
  linear_combination (norm := module) -h

theorem curvature_sub_right (X Y Z₁ Z₂ : SmoothVectorField I M) (p : M) :
    (nabla.curvature X Y (Z₁ - Z₂)) p
      = (nabla.curvature X Y Z₁) p - (nabla.curvature X Y Z₂) p := by
  have h := nabla.curvature_add_right X Y (Z₁ - Z₂) Z₂ p
  have e : (Z₁ - Z₂) + Z₂ = Z₁ := by ext q; simp
  rw [e] at h
  linear_combination (norm := module) -h

/-! ## Pointwise dependence of the curvature -/

/-- **Math.** do Carmo Ch. 4, Prop. 2.2 read pointwise: the value `R(X,Y)Z|_p`
depends only on `X(p), Y(p), Z(p)` — the tensoriality of the curvature operator. -/
theorem curvature_apply_congr {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : SmoothVectorField I M} {p : M}
    (hX : X₁ p = X₂ p) (hY : Y₁ p = Y₂ p) (hZ : Z₁ p = Z₂ p) :
    (nabla.curvature X₁ Y₁ Z₁) p = (nabla.curvature X₂ Y₂ Z₂) p := by
  have step1 : (nabla.curvature X₁ Y₁ Z₁) p = (nabla.curvature X₂ Y₁ Z₁) p := by
    have h := nabla.curvature_sub_left X₁ X₂ Y₁ Z₁ p
    have h0 : (nabla.curvature (X₁ - X₂) Y₁ Z₁) p = 0 :=
      nabla.curvature_apply_eq_zero_of_apply_eq_zero_left Y₁ Z₁
        (show (X₁ - X₂) p = 0 by rw [SmoothVectorField.sub_apply, hX, sub_self])
    rw [h0] at h; exact sub_eq_zero.mp h.symm
  have step2 : (nabla.curvature X₂ Y₁ Z₁) p = (nabla.curvature X₂ Y₂ Z₁) p := by
    have h := nabla.curvature_sub_middle X₂ Y₁ Y₂ Z₁ p
    have h0 : (nabla.curvature X₂ (Y₁ - Y₂) Z₁) p = 0 :=
      nabla.curvature_apply_eq_zero_of_apply_eq_zero_middle X₂ Z₁
        (show (Y₁ - Y₂) p = 0 by rw [SmoothVectorField.sub_apply, hY, sub_self])
    rw [h0] at h; exact sub_eq_zero.mp h.symm
  have step3 : (nabla.curvature X₂ Y₂ Z₁) p = (nabla.curvature X₂ Y₂ Z₂) p := by
    have h := nabla.curvature_sub_right X₂ Y₂ Z₁ Z₂ p
    have h0 : (nabla.curvature X₂ Y₂ (Z₁ - Z₂)) p = 0 :=
      nabla.curvature_apply_eq_zero_of_apply_eq_zero_right X₂ Y₂
        (show (Z₁ - Z₂) p = 0 by rw [SmoothVectorField.sub_apply, hZ, sub_self])
    rw [h0] at h; exact sub_eq_zero.mp h.symm
  exact (step1.trans step2).trans step3

/-! ## The pointwise curvature operator and its `(0,4)` form -/

/-- **Math.** A smooth global field extending a given tangent vector at `p` (the choice is immaterial by tensoriality of the curvature, `curvature_apply_congr`). -/
def extendField (p : M) (v : TangentSpace I p) : SmoothVectorField I M :=
  (exists_smoothVectorField_eq p v).choose

@[simp] theorem extendField_apply (p : M) (v : TangentSpace I p) :
    extendField p v p = v :=
  (exists_smoothVectorField_eq p v).choose_spec

/-- **Math.** The **pointwise curvature operator** `R : T_pM³ → T_pM`: the value
of `R(X,Y)Z` at `p` for any smooth extensions of the given tangent vectors,
well-defined by `curvature_apply_congr`. -/
def curvatureOperatorAt (p : M) (u v w : TangentSpace I p) : TangentSpace I p :=
  (nabla.curvature (extendField p u) (extendField p v) (extendField p w)) p

/-- **Math.** The defining property of the pointwise curvature operator: it is the value of `R(X,Y)Z` at `p` for *any* smooth extensions of the tangent vectors. -/
theorem curvatureOperatorAt_eq (p : M) {u v w : TangentSpace I p}
    {X Y Z : SmoothVectorField I M} (hX : X p = u) (hY : Y p = v) (hZ : Z p = w) :
    nabla.curvatureOperatorAt p u v w = (nabla.curvature X Y Z) p := by
  rw [curvatureOperatorAt]
  exact nabla.curvature_apply_congr (by simp [hX]) (by simp [hY]) (by simp [hZ])

/-- **Math.** The **pointwise curvature `(0,4)` form** `⟨R(x,y)z, t⟩_g` on `T_pM`,
the metric-lowered pointwise curvature operator. -/
def curvatureFormAt (g : RiemannianMetric I M) (p : M) (x y z t : TangentSpace I p) : ℝ :=
  g.metricInner p (nabla.curvatureOperatorAt p x y z) t

/-- **Math.** The pointwise `(0,4)` form is computed from *any* smooth extensions
of the four tangent vectors: `curvatureFormAt g p (Xp)(Yp)(Zp)(Tp) = ⟨R(X,Y)Z,T⟩_g|_p`. -/
theorem curvatureFormAt_eq (g : RiemannianMetric I M) (p : M) {x y z t : TangentSpace I p}
    {X Y Z T : SmoothVectorField I M} (hX : X p = x) (hY : Y p = y)
    (hZ : Z p = z) (hT : T p = t) :
    nabla.curvatureFormAt g p x y z t = nabla.curvatureForm g X Y Z T p := by
  show g.metricInner p (nabla.curvatureOperatorAt p x y z) t = _
  rw [nabla.curvatureOperatorAt_eq p hX hY hZ]
  show g.metricInner p ((nabla.curvature X Y Z) p) t
    = g.metricInner p ((nabla.curvature X Y Z) p) (T p)
  rw [hT]

/-- **Math.** do Carmo Ch. 4, Prop. 2.5, read pointwise: for the Levi-Civita
connection the pointwise curvature `(0,4)` form `⟨R(x,y)z, t⟩_g` on `T_pM` is an
**algebraic curvature form** (multilinear, antisymmetric in each pair, first
Bianchi). This is the bridge from the field-level curvature symmetries to the
pointwise linear algebra of sectional curvature (`IsAlgCurvatureForm`). The inner
product on the fibre `T_pM` is the one induced by `g` (the `RiemannianBundle`
instance of `g`, for which `⟪·,·⟫ = g.metricInner p`). -/
theorem isAlgCurvatureForm_curvatureFormAt (g : RiemannianMetric I M)
    (hLC : nabla.IsLeviCivita g) (p : M) :
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    IsAlgCurvatureForm (nabla.curvatureFormAt g p) := by
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨hsym, hcompat⟩ := hLC
  have hT4 := nabla.curvatureForm_isCovariantTensor4 g
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- additivity in the first slot
    intro x₁ x₂ y z t
    rw [nabla.curvatureFormAt_eq g p (X := extendField p x₁ + extendField p x₂)
        (by rw [SmoothVectorField.add_apply, extendField_apply, extendField_apply])
        (extendField_apply p y) (extendField_apply p z) (extendField_apply p t),
      nabla.curvatureFormAt_eq g p (extendField_apply p x₁) (extendField_apply p y)
        (extendField_apply p z) (extendField_apply p t),
      nabla.curvatureFormAt_eq g p (extendField_apply p x₂) (extendField_apply p y)
        (extendField_apply p z) (extendField_apply p t)]
    exact hT4.add₁ (extendField p x₁) (extendField p x₂) (extendField p y)
      (extendField p z) (extendField p t) p
  · -- homogeneity in the first slot
    intro a x y z t
    rw [nabla.curvatureFormAt_eq g p
        (X := SmoothVectorField.smul (fun _ => a) contMDiff_const (extendField p x))
        (by rw [SmoothVectorField.smul_apply, extendField_apply])
        (extendField_apply p y) (extendField_apply p z) (extendField_apply p t),
      nabla.curvatureFormAt_eq g p (extendField_apply p x) (extendField_apply p y)
        (extendField_apply p z) (extendField_apply p t)]
    exact hT4.smul₁ (fun _ => a) contMDiff_const (extendField p x) (extendField p y)
      (extendField p z) (extendField p t) p
  · -- antisymmetry in the first pair
    intro x y z t
    rw [nabla.curvatureFormAt_eq g p (extendField_apply p x) (extendField_apply p y)
        (extendField_apply p z) (extendField_apply p t),
      nabla.curvatureFormAt_eq g p (extendField_apply p y) (extendField_apply p x)
        (extendField_apply p z) (extendField_apply p t)]
    exact nabla.curvatureForm_antisymm_left g (extendField p x) (extendField p y)
      (extendField p z) (extendField p t) p
  · -- antisymmetry in the second pair
    intro x y z t
    rw [nabla.curvatureFormAt_eq g p (extendField_apply p x) (extendField_apply p y)
        (extendField_apply p z) (extendField_apply p t),
      nabla.curvatureFormAt_eq g p (extendField_apply p x) (extendField_apply p y)
        (extendField_apply p t) (extendField_apply p z)]
    exact nabla.curvatureForm_antisymm_right g hcompat (extendField p x) (extendField p y)
      (extendField p z) (extendField p t) p
  · -- first Bianchi identity
    intro x y z t
    rw [nabla.curvatureFormAt_eq g p (extendField_apply p x) (extendField_apply p y)
        (extendField_apply p z) (extendField_apply p t),
      nabla.curvatureFormAt_eq g p (extendField_apply p y) (extendField_apply p z)
        (extendField_apply p x) (extendField_apply p t),
      nabla.curvatureFormAt_eq g p (extendField_apply p z) (extendField_apply p x)
        (extendField_apply p y) (extendField_apply p t)]
    exact nabla.curvatureForm_bianchi g hsym (extendField p x) (extendField p y)
      (extendField p z) (extendField p t) p

end AffineConnection

end Riemannian
