import OpenGALib.Riemannian.Manifold.DoCarmoCh4Tensor
import OpenGALib.Riemannian.Manifold.DoCarmoCh4Ricci
import OpenGALib.Riemannian.Manifold.DoCarmoCh6Locality

/-!
# Morgan–Tian Ch. 1, §"Curvature of a Riemannian manifold" — pointwise curvature

Morgan–Tian's Riemann curvature tensor (blueprint `def:riemann-curvature-tensor`)
is a *tensor*: its value at a point `p` depends only on the values of its vector
field arguments at `p`. This file provides the bridge from OpenGALib's
vector-field-level curvature 4-tensor `Riemannian.AffineConnection.curvatureForm`
to a genuine pointwise (fiberwise) function of tangent *vectors*:

* the bump-function locality engine for scalar-valued `𝒟(M)`-linear slots
  (`tensorial_congr_apply`) and its 4-slot consequence
  (`covariantTensor4_congr_apply`): a covariant 4-tensor evaluated at `p` only
  sees the values of its arguments at `p`;
* `curvatureFormAt g nabla p : (T_pM)⁴ → ℝ`, the curvature `(0,4)`-tensor as a
  function of tangent vectors, defined via arbitrary global extensions and
  well defined by locality (`curvatureFormAt_eq`);
* the four symmetries of `claim:curvature-symmetries-bianchi` at the pointwise
  level, packaged as `Riemannian.IsAlgCurvatureForm` on the tangent space
  `T_pM` equipped with the inner product of `g`
  (`isAlgCurvatureForm_curvatureFormAt`), with the sanity check that the
  installed inner product on `T_pM` is definitionally `g.metricInner p`
  (`inner_tangentSpace_eq_metricInner`);
* the manifold-level **sectional curvature** `sectionalCurvatureAt`
  (blueprint `def:sectional-curvature`) and **Ricci curvature** `ricciAt`
  (blueprint `def:ricci-curvature`) obtained by specializing OpenGALib's
  algebraic `Riemannian.sectionalCurvature` / `Riemannian.ricciForm` to
  `curvatureFormAt`.

**Sign conventions.** Morgan–Tian's curvature operator
`ℛ_MT(X,Y)Z = ∇_X∇_Y Z − ∇_Y∇_X Z − ∇_{[X,Y]}Z` is the *negative* of
OpenGALib's do Carmo-convention `Riemannian.AffineConnection.curvature`, and
Morgan–Tian's `(0,4)`-tensor is `ℛ_MT(X,Y,Z,W) = g(ℛ_MT(X,Y)W, Z)` (note the
swap of the last two variables). The two sign flips cancel:
`ℛ_MT(X,Y,Z,W) = curvatureForm X Y Z W`, so `curvatureFormAt` below *is*
Morgan–Tian's pointwise `(0,4)` curvature tensor.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1
(blueprint `def:riemann-curvature-tensor`, `claim:curvature-symmetries-bianchi`,
`def:sectional-curvature`, `def:ricci-curvature`).
-/

open scoped ContDiff Manifold Topology Bundle
open Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

/-! ### The locality engine for a single `𝒟(M)`-linear scalar slot

Morgan–Tian's proof of `claim:curvature-symmetries-bianchi` uses "repeatedly
that all the expressions involved are tensorial", i.e. that a `𝒟(M)`-linear
slot of a scalar-valued form only sees the value of its argument at the point.
We prove this once for an abstract slot `S : 𝒳(M) → 𝒟(M)` that is additive and
`𝒟(M)`-homogeneous, mirroring the bump-function argument of
`Riemannian.AffineConnection.cov_congr_apply_left`. -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** An additive scalar slot kills the zero field: `S(0)(q) = 0`.
Blueprint: `def:riemann-curvature-tensor` (tensoriality infrastructure). -/
theorem tensorial_zero_apply (S : SmoothVectorField I M → M → ℝ)
    (hadd : ∀ (X Y : SmoothVectorField I M) (q : M), S (X + Y) q = S X q + S Y q)
    (q : M) : S 0 q = 0 := by
  have e : (0 : SmoothVectorField I M) + 0 = 0 := by ext r; simp
  have h := hadd 0 0 q
  rw [e] at h
  linarith

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** An additive scalar slot is subtractive:
`S(X − Y)(q) = S(X)(q) − S(Y)(q)`.
Blueprint: `def:riemann-curvature-tensor` (tensoriality infrastructure). -/
theorem tensorial_sub_apply (S : SmoothVectorField I M → M → ℝ)
    (hadd : ∀ (X Y : SmoothVectorField I M) (q : M), S (X + Y) q = S X q + S Y q)
    (X Y : SmoothVectorField I M) (q : M) :
    S (X - Y) q = S X q - S Y q := by
  have e : (X - Y) + Y = X := by ext r; simp
  have h := hadd (X - Y) Y q
  rw [e] at h
  linarith

omit [CompleteSpace E] [SigmaCompactSpace M] in
/-- **Math.** A `𝒟(M)`-homogeneous scalar slot annihilates, at `p`, fields
vanishing near `p` — the bump-function cutoff trick.
Blueprint: `def:riemann-curvature-tensor` (tensoriality infrastructure). -/
theorem tensorial_apply_eq_zero_of_eventuallyEq_zero
    (S : SmoothVectorField I M → M → ℝ)
    (hsmul : ∀ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
      (X : SmoothVectorField I M) (q : M),
      S (SmoothVectorField.smul f hf X) q = f q * S X q)
    {τ : SmoothVectorField I M} {p : M} (hτ : ∀ᶠ q in nhds p, τ q = 0) :
    S τ p = 0 := by
  obtain ⟨f, hf, hfp, hfτ⟩ := exists_smul_eq_self_of_eventuallyEq_zero hτ
  have h := hsmul f hf τ p
  rw [hfτ, hfp, zero_mul] at h
  exact h

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** An additive, `𝒟(M)`-homogeneous scalar slot annihilates, at `p`,
fields that are (pointwise) finite sums `Σᵢ fᵢ Wᵢ` with all scalars vanishing
at `p` — the finite-sum core of tensoriality.
Blueprint: `def:riemann-curvature-tensor` (tensoriality infrastructure). -/
theorem tensorial_apply_eq_zero_of_forall_eq_sum
    (S : SmoothVectorField I M → M → ℝ)
    (hadd : ∀ (X Y : SmoothVectorField I M) (q : M), S (X + Y) q = S X q + S Y q)
    (hsmul : ∀ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
      (X : SmoothVectorField I M) (q : M),
      S (SmoothVectorField.smul f hf X) q = f q * S X q)
    {ι : Type*} (s : Finset ι) {f : ι → M → ℝ}
    (hf : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f i)) (W : ι → SmoothVectorField I M)
    {p : M} (hfp : ∀ i ∈ s, f i p = 0) {σ : SmoothVectorField I M}
    (hσ : ∀ q, σ q = ∑ i ∈ s, f i q • W i q) :
    S σ p = 0 := by
  classical
  induction s using Finset.induction_on generalizing σ with
  | empty =>
    have hσ0 : σ = 0 := SmoothVectorField.ext fun q => by simpa using hσ q
    rw [hσ0]
    exact tensorial_zero_apply S hadd p
  | @insert a s ha ih =>
    have key : ∀ q, (σ - SmoothVectorField.smul (f a) (hf a) (W a)) q
        = ∑ i ∈ s, f i q • W i q := by
      intro q
      rw [SmoothVectorField.sub_apply, SmoothVectorField.smul_apply, hσ q,
        Finset.sum_insert ha]
      abel
    have hzero := ih (fun i hi => hfp i (Finset.mem_insert_of_mem hi)) key
    have hsub := tensorial_sub_apply S hadd σ
      (SmoothVectorField.smul (f a) (hf a) (W a)) p
    have hsm := hsmul (f a) (hf a) (W a) p
    rw [hsub, hsm, hfp a (Finset.mem_insert_self a s), zero_mul, sub_zero] at hzero
    exact hzero

omit [CompleteSpace E] in
/-- **Math.** An additive, `𝒟(M)`-homogeneous scalar slot annihilates, at `p`,
any field vanishing *at* `p`: decompose `σ = Σᵢ fᵢ Wᵢ + τ` by the bump-frame
decomposition, kill the sum by homogeneity and the remainder by the cutoff.
Blueprint: `def:riemann-curvature-tensor` (tensoriality infrastructure). -/
theorem tensorial_apply_eq_zero (S : SmoothVectorField I M → M → ℝ)
    (hadd : ∀ (X Y : SmoothVectorField I M) (q : M), S (X + Y) q = S X q + S Y q)
    (hsmul : ∀ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
      (X : SmoothVectorField I M) (q : M),
      S (SmoothVectorField.smul f hf X) q = f q * S X q)
    {σ : SmoothVectorField I M} {p : M} (hσ : σ p = 0) :
    S σ p = 0 := by
  obtain ⟨k, f, hf, W, τ, hfp, hτ0, hdecomp⟩ :=
    exists_decomposition_of_apply_eq_zero σ hσ
  have hkey : ∀ q, (σ - τ) q = ∑ i, f i q • W i q := by
    intro q
    rw [SmoothVectorField.sub_apply, hdecomp q]
    abel
  have h1 : S (σ - τ) p = 0 :=
    tensorial_apply_eq_zero_of_forall_eq_sum S hadd hsmul Finset.univ hf W
      (fun i _ => hfp i) hkey
  have h2 : S τ p = 0 :=
    tensorial_apply_eq_zero_of_eventuallyEq_zero S hsmul hτ0
  have h3 := tensorial_sub_apply S hadd σ τ p
  rw [h1] at h3
  linarith

omit [CompleteSpace E] in
/-- **Math.** **Pointwise locality of a `𝒟(M)`-linear scalar slot**: if
`X(p) = X'(p)` then `S(X)(p) = S(X')(p)`. This is the abstract form of
Morgan–Tian's "all the expressions involved are tensorial".
Blueprint: `def:riemann-curvature-tensor` (tensoriality infrastructure). -/
theorem tensorial_congr_apply (S : SmoothVectorField I M → M → ℝ)
    (hadd : ∀ (X Y : SmoothVectorField I M) (q : M), S (X + Y) q = S X q + S Y q)
    (hsmul : ∀ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
      (X : SmoothVectorField I M) (q : M),
      S (SmoothVectorField.smul f hf X) q = f q * S X q)
    {X X' : SmoothVectorField I M} {p : M} (h : X p = X' p) :
    S X p = S X' p := by
  have hσ : (X - X') p = 0 := by
    rw [SmoothVectorField.sub_apply, h, sub_self]
  have h0 := tensorial_apply_eq_zero S hadd hsmul hσ
  have hsub := tensorial_sub_apply S hadd X X' p
  linarith

omit [CompleteSpace E] in
/-- **Math.** **Pointwise locality of a covariant 4-tensor**: the value
`T(X,Y,Z,W)(p)` of a covariant tensor of order 4 depends only on the values
`X(p), Y(p), Z(p), W(p)` of its arguments at `p`. Apply the one-slot locality
engine to each slot in turn.
Blueprint: `def:riemann-curvature-tensor`. -/
theorem covariantTensor4_congr_apply
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ))
    (hT : IsCovariantTensor4 T)
    {X X' Y Y' Z Z' W W' : SmoothVectorField I M} {p : M}
    (hX : X p = X' p) (hY : Y p = Y' p) (hZ : Z p = Z' p) (hW : W p = W' p) :
    T X Y Z W p = T X' Y' Z' W' p := by
  have h1 : T X Y Z W p = T X' Y Z W p :=
    tensorial_congr_apply (fun A => T A Y Z W)
      (fun A B q => hT.add₁ A B Y Z W q)
      (fun f hf A q => hT.smul₁ f hf A Y Z W q) hX
  have h2 : T X' Y Z W p = T X' Y' Z W p :=
    tensorial_congr_apply (fun A => T X' A Z W)
      (fun A B q => hT.add₂ X' A B Z W q)
      (fun f hf A q => hT.smul₂ f hf X' A Z W q) hY
  have h3 : T X' Y' Z W p = T X' Y' Z' W p :=
    tensorial_congr_apply (fun A => T X' Y' A W)
      (fun A B q => hT.add₃ X' Y' A B W q)
      (fun f hf A q => hT.smul₃ f hf X' Y' A W q) hZ
  have h4 : T X' Y' Z' W p = T X' Y' Z' W' p :=
    tensorial_congr_apply (fun A => T X' Y' Z' A)
      (fun A B q => hT.add₄ X' Y' Z' A B q)
      (fun f hf A q => hT.smul₄ f hf X' Y' Z' A q) hW
  rw [h1, h2, h3, h4]

/-! ### Extending a tangent vector to a global field -/

/-- **Math.** A chosen global smooth vector field through the tangent vector
`v ∈ T_pM` (`extendVector p v p = v`), via the partition-of-unity extension
`Riemannian.exists_smoothVectorField_eq`. Used to evaluate vector-field-level
tensors on raw tangent vectors.
Blueprint: `def:riemann-curvature-tensor` (pointwise evaluation
infrastructure). -/
noncomputable def extendVector (p : M) (v : TangentSpace I p) :
    SmoothVectorField I M :=
  Classical.choose (exists_smoothVectorField_eq p v)

omit [CompleteSpace E] in
/-- **Math.** The defining property of `extendVector`: it passes through `v`
at `p`. Blueprint: `def:riemann-curvature-tensor`. -/
@[simp] theorem extendVector_apply (p : M) (v : TangentSpace I p) :
    extendVector p v p = v :=
  Classical.choose_spec (exists_smoothVectorField_eq p v)

/-! ### The pointwise curvature `(0,4)`-tensor -/

/-- **Math.** Morgan–Tian's **Riemann curvature `(0,4)`-tensor as a pointwise
tensor**: for tangent vectors `v, w, z, t ∈ T_pM`,
`curvatureFormAt g ∇ p v w z t = ⟨R(V,W)Z, T⟩(p)` for any global extensions
`V, W, Z, T` of the four vectors (well defined by
`covariantTensor4_congr_apply`; the chosen extensions are `extendVector`).
By the sign discussion in the module docstring this equals Morgan–Tian's
`ℛ(X,Y,Z,W) = g(ℛ_MT(X,Y)W, Z)` evaluated at `(v,w,z,t)`.
Blueprint: `def:riemann-curvature-tensor`. -/
noncomputable def curvatureFormAt (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (v w z t : TangentSpace I p) : ℝ :=
  nabla.curvatureForm g (extendVector p v) (extendVector p w)
    (extendVector p z) (extendVector p t) p

/-- **Math.** Unfolding lemma for `curvatureFormAt` in terms of the chosen
extensions. Blueprint: `def:riemann-curvature-tensor`. -/
theorem curvatureFormAt_def (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (v w z t : TangentSpace I p) :
    curvatureFormAt g nabla p v w z t
      = nabla.curvatureForm g (extendVector p v) (extendVector p w)
          (extendVector p z) (extendVector p t) p := rfl

/-- **Math.** **The pointwise curvature tensor evaluates vector fields
pointwise**: for any smooth vector fields `X, Y, Z, W`,
`curvatureFormAt g ∇ p (X p) (Y p) (Z p) (W p) = ⟨R(X,Y)Z, W⟩(p)`. This is the
statement that the curvature 4-tensor at `p` depends only on the values of its
arguments at `p` — Morgan–Tian's tensoriality of `ℛ`.
Blueprint: `def:riemann-curvature-tensor`. -/
theorem curvatureFormAt_eq [I.Boundaryless] (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (X Y Z W : SmoothVectorField I M) (p : M) :
    curvatureFormAt g nabla p (X p) (Y p) (Z p) (W p)
      = nabla.curvatureForm g X Y Z W p := by
  rw [curvatureFormAt_def]
  exact covariantTensor4_congr_apply _ (nabla.curvatureForm_isCovariantTensor4 g)
    (extendVector_apply p (X p)) (extendVector_apply p (Y p))
    (extendVector_apply p (Z p)) (extendVector_apply p (W p))

/-! ### Multilinearity and the curvature symmetries, pointwise -/

/-- **Math.** `curvatureFormAt` is additive in its first slot.
Blueprint: `def:riemann-curvature-tensor`. -/
theorem curvatureFormAt_add_left [I.Boundaryless] (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (v₁ v₂ w z t : TangentSpace I p) :
    curvatureFormAt g nabla p (v₁ + v₂) w z t
      = curvatureFormAt g nabla p v₁ w z t
        + curvatureFormAt g nabla p v₂ w z t := by
  have hT := nabla.curvatureForm_isCovariantTensor4 g
  have h1 : nabla.curvatureForm g (extendVector p (v₁ + v₂)) (extendVector p w)
        (extendVector p z) (extendVector p t) p
      = nabla.curvatureForm g (extendVector p v₁ + extendVector p v₂)
          (extendVector p w) (extendVector p z) (extendVector p t) p :=
    covariantTensor4_congr_apply _ hT (by simp) rfl rfl rfl
  simp only [curvatureFormAt_def]
  rw [h1, hT.add₁]

/-- **Math.** `curvatureFormAt` is `ℝ`-homogeneous in its first slot.
Blueprint: `def:riemann-curvature-tensor`. -/
theorem curvatureFormAt_smul_left [I.Boundaryless] (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (a : ℝ) (v w z t : TangentSpace I p) :
    curvatureFormAt g nabla p (a • v) w z t
      = a * curvatureFormAt g nabla p v w z t := by
  have hT := nabla.curvatureForm_isCovariantTensor4 g
  have hconst : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => a) := contMDiff_const
  have h1 : nabla.curvatureForm g (extendVector p (a • v)) (extendVector p w)
        (extendVector p z) (extendVector p t) p
      = nabla.curvatureForm g
          (SmoothVectorField.smul (fun _ => a) hconst (extendVector p v))
          (extendVector p w) (extendVector p z) (extendVector p t) p :=
    covariantTensor4_congr_apply _ hT (by simp) rfl rfl rfl
  simp only [curvatureFormAt_def]
  rw [h1, hT.smul₁]

/-- **Math.** Antisymmetry of the pointwise curvature tensor in its first pair
(Morgan–Tian `R_{ijkl} = −R_{jikl}`).
Blueprint: `claim:curvature-symmetries-bianchi`. -/
theorem curvatureFormAt_antisymm_left (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (v w z t : TangentSpace I p) :
    curvatureFormAt g nabla p v w z t = -curvatureFormAt g nabla p w v z t :=
  nabla.curvatureForm_antisymm_left g _ _ _ _ p

/-- **Math.** Antisymmetry of the pointwise curvature tensor in its second pair
(Morgan–Tian `R_{ijkl} = −R_{ijlk}`), for a metric-compatible connection.
Blueprint: `claim:curvature-symmetries-bianchi`. -/
theorem curvatureFormAt_antisymm_right [I.Boundaryless] (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hcompat : nabla.IsMetricCompatible g)
    (p : M) (v w z t : TangentSpace I p) :
    curvatureFormAt g nabla p v w z t = -curvatureFormAt g nabla p v w t z :=
  nabla.curvatureForm_antisymm_right g hcompat _ _ _ _ p

/-- **Math.** The first Bianchi identity for the pointwise curvature tensor
(Morgan–Tian: the cyclic sum over the first three slots vanishes), for a
symmetric (torsion-free) connection.
Blueprint: `claim:curvature-symmetries-bianchi`. -/
theorem curvatureFormAt_bianchi (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hsym : nabla.IsSymmetric)
    (p : M) (v w z t : TangentSpace I p) :
    curvatureFormAt g nabla p v w z t + curvatureFormAt g nabla p w z v t
      + curvatureFormAt g nabla p z v w t = 0 :=
  nabla.curvatureForm_bianchi g hsym _ _ _ _ p

/-! ### The algebraic curvature form on each tangent space

We equip the fibre `T_pM` with the inner product of `g` through Mathlib's
`Bundle.RiemannianBundle` route (the diamond-free construction), exactly as in
`Riemannian.instRiemannianBundleOfHasMetric`. -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Sanity check: under the `Bundle.RiemannianBundle` instances
induced by `g`, the inner product on `T_pM` is *definitionally* `g.metricInner
p`. This guarantees that the algebraic sectional/Ricci curvature below are
computed against the metric `g` itself.
Blueprint: `def:riemannian-metric` / `def:sectional-curvature`. -/
theorem inner_tangentSpace_eq_metricInner (g : RiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    inner ℝ v w = g.metricInner p v w := rfl

/-- **Math.** For a Levi-Civita connection, the pointwise curvature tensor at
`p` is an **algebraic curvature form** on the inner product space
`(T_pM, g_p)`: it is quadrilinear, antisymmetric in the first and in the second
pair, and satisfies the first Bianchi identity. This packages Morgan–Tian's
curvature symmetries as a fiberwise structure, unlocking the purely algebraic
theory (sectional curvature determines the tensor, Ricci trace, etc.).
Blueprint: `claim:curvature-symmetries-bianchi`. -/
theorem isAlgCurvatureForm_curvatureFormAt [I.Boundaryless]
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    IsAlgCurvatureForm (curvatureFormAt g nabla p) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact
    { add_left := fun v₁ v₂ w z t => curvatureFormAt_add_left g nabla p v₁ v₂ w z t
      smul_left := fun a v w z t => curvatureFormAt_smul_left g nabla p a v w z t
      antisymm₁₂ := fun v w z t => curvatureFormAt_antisymm_left g nabla p v w z t
      antisymm₃₄ := fun v w z t =>
        curvatureFormAt_antisymm_right g nabla hLC.2 p v w z t
      bianchi := fun v w z t => curvatureFormAt_bianchi g nabla hLC.1 p v w z t }

/-! ### Sectional and Ricci curvature as manifold-level notions -/

/-- **Math.** The **sectional curvature** at `p ∈ M` of the pair `(v, w)` of
tangent vectors: `K(v,w) = ℛ(v,w,v,w) / (|v|²|w|² − ⟨v,w⟩²)`, computed against
the inner product `g_p` on `T_pM`. For `{v, w}` an orthonormal basis of a
2-plane `P ⊂ T_pM` the denominator is `1` and this is Morgan–Tian's
`K(P) = ℛ(X,Y,X,Y)`; by `Riemannian.IsAlgCurvatureForm.sectionalCurvature_changeBasis`
the value depends only on the plane spanned.
Blueprint: `def:sectional-curvature`. -/
noncomputable def sectionalCurvatureAt (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (v w : TangentSpace I p) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  sectionalCurvature (curvatureFormAt g nabla p) v w

/-- **Math.** The **Ricci curvature tensor** at `p ∈ M`: the symmetric bilinear
form `Ric_p(v,w) = Σᵢ ℛ(v,eᵢ,w,eᵢ)` for any orthonormal basis `{eᵢ}` of
`(T_pM, g_p)`, defined basis-free as the trace of the Riesz endomorphism of
`(z,t) ↦ ℛ(v,z,w,t)` (`Riemannian.ricciForm`; the orthonormal-basis formula is
`Riemannian.ricciForm_eq_sum`). Requires the Levi-Civita hypothesis through the
symmetries packaged in `isAlgCurvatureForm_curvatureFormAt`.
Blueprint: `def:ricci-curvature`. -/
noncomputable def ricciAt [I.Boundaryless] (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) (p : M)
    (v w : TangentSpace I p) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ricciForm (isAlgCurvatureForm_curvatureFormAt g nabla hLC p) v w

end MorganTianLib
