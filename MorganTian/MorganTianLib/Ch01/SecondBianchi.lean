import OpenGALib.Riemannian.Manifold.DoCarmoCh4Tensor

/-!
# Poincaré Ch. 1, §1.2 — The second Bianchi identity

Formalizes, for Morgan–Tian's Ch. 1 preliminaries, the covariant differential
of the curvature `(0,4)`-tensor and the **second Bianchi identity**
`R_{ijkl,h} + R_{ijlh,k} + R_{ijhk,l} = 0` from blueprint
`claim:curvature-symmetries-bianchi`, at the smooth-vector-field level.

**Conventions.** OpenGALib's curvature operator follows do Carmo's sign
convention, `R_dC(X,Y)Z = ∇_Y ∇_X Z − ∇_X ∇_Y Z + ∇_{[X,Y]} Z`, which is
*minus* Morgan–Tian's `R_MT(X,Y)Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z`.
Morgan–Tian's `(0,4)`-tensor is `R_MT(X,Y,Z,W) = g(R_MT(X,Y)W, Z)` (note the
transposition of the last two slots), while OpenGALib's is
`nabla.curvatureForm g X Y Z W (p) = g(R_dC(X,Y)Z (p), W(p))`. For a
metric-compatible connection the operator sign flip and the slot
transposition cancel, so the two `(0,4)`-tensors agree *slotwise*:
`R_MT(X,Y,Z,W) = nabla.curvatureForm g X Y Z W` (this bridge is
`MorganTianLib.curvatureForm_eq` in `MorganTianLib.Ch01.CurvatureTensor`). All
results below are therefore stated for `nabla.curvatureForm g`, and the index
translation is `R_{ijkl} = nabla.curvatureForm g ∂_i ∂_j ∂_k ∂_l`; the
covariant derivative index `h` of `R_{ijkl,h} = (∇_{∂_h} R)_{ijkl}` is the
**last** (fifth) slot of `covariantDifferential4`.

Following the blueprint proof (`claim:curvature-symmetries-bianchi`, second
Bianchi step), the identity is proved by
1. the **operator-level second Bianchi identity**
   `(∇_U R)(X,Y)Z + (∇_X R)(Y,U)Z + (∇_Y R)(U,X)Z = 0`
   (`covariantDerivCurvature_cyclic`), using only torsion-freeness, the
   Jacobi identity for the Lie bracket, and the antisymmetry
   `R(X,Y) = −R(Y,X)`;
2. pairing with the metric via metric compatibility
   (`covariantDifferential4_curvatureForm_apply`), which gives the cyclic
   identity over slots `(1, 2, 5)`
   (`covariantDifferential4_curvatureForm_cyclic_first_pair`);
3. the pair-swap symmetry `R(X,Y,Z,W) = R(Z,W,X,Y)`, inherited by the
   covariant differential
   (`covariantDifferential4_curvatureForm_pairSwap`), which moves the cyclic
   sum to slots `(3, 4, 5)` — Morgan–Tian's `(k, l, h)` — giving the final
   statement `secondBianchi`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.2
(blueprint `claim:curvature-symmetries-bianchi`).
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace MorganTianLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The covariant differential of an order-4 covariant tensor -/

/-- **Math.** The **covariant differential** `∇T` of an order-4 covariant
tensor `T : 𝒳(M)⁴ → 𝒟(M)`, an order-5 tensor defined (do Carmo Ch. 4,
Def. 5.7, extended from `Riemannian.AffineConnection.covariantDifferential2`)
by
`∇T(X, Y, Z, W; U) = U(T(X,Y,Z,W)) − T(∇_U X, Y, Z, W) − T(X, ∇_U Y, Z, W)
− T(X, Y, ∇_U Z, W) − T(X, Y, Z, ∇_U W)`,
with the differentiation direction `U` in the **last** slot. Applied to the
curvature `(0,4)`-tensor this is Morgan–Tian's
`R_{ijkl,h} = (∇_{∂_h} R)_{ijkl}` with `(X,Y,Z,W;U) = (∂_i,∂_j,∂_k,∂_l;∂_h)`.

Blueprint: `claim:curvature-symmetries-bianchi`. -/
def covariantDifferential4 (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ))
    (X Y Z W U : SmoothVectorField I M) : M → ℝ :=
  fun p => U.dir (T X Y Z W) p - T (nabla.cov U X) Y Z W p - T X (nabla.cov U Y) Z W p
    - T X Y (nabla.cov U Z) W p - T X Y Z (nabla.cov U W) p

/-! ### Algebraic helpers for the curvature operator -/

/-- **Math.** The curvature operator is subtractive in its first slot,
`R(X₁ − X₂, Y)Z = R(X₁,Y)Z − R(X₂,Y)Z`, pointwise. Immediate from additivity
(`Riemannian.AffineConnection.curvature_add_left`), needed to split
`R([X,Y], U)Z` along torsion-freeness `[X,Y] = ∇_X Y − ∇_Y X`.

Blueprint: `claim:curvature-symmetries-bianchi` (proof step 6). -/
theorem curvature_sub_left (nabla : AffineConnection I M)
    (X₁ X₂ Y Z : SmoothVectorField I M) (p : M) :
    (nabla.curvature (X₁ - X₂) Y Z) p
      = (nabla.curvature X₁ Y Z) p - (nabla.curvature X₂ Y Z) p := by
  have h := nabla.curvature_add_left (X₁ - X₂) X₂ Y Z p
  have e : (X₁ - X₂) + X₂ = X₁ := by ext q; simp
  rw [e] at h
  linear_combination (norm := module) -h

/-- **Math.** Pointwise expansion of the covariant derivative of a curvature
field: `∇_U (R(X,Y)Z) = ∇_U ∇_Y ∇_X Z − ∇_U ∇_X ∇_Y Z + ∇_U ∇_{[X,Y]} Z`
(do Carmo sign convention). Pure bookkeeping from additivity of `∇` in its
second slot.

Blueprint: `claim:curvature-symmetries-bianchi` (proof step 6). -/
theorem cov_curvature_apply (nabla : AffineConnection I M)
    (U X Y Z : SmoothVectorField I M) (p : M) :
    (nabla.cov U (nabla.curvature X Y Z)) p
      = (nabla.cov U (nabla.cov Y (nabla.cov X Z))) p
        - (nabla.cov U (nabla.cov X (nabla.cov Y Z))) p
        + (nabla.cov U (nabla.cov (bracketField X Y) Z)) p := by
  have h : nabla.cov U (nabla.curvature X Y Z)
      = nabla.cov U (nabla.cov Y (nabla.cov X Z) - nabla.cov X (nabla.cov Y Z))
        + nabla.cov U (nabla.cov (bracketField X Y) Z) :=
    nabla.add_right U (nabla.cov Y (nabla.cov X Z) - nabla.cov X (nabla.cov Y Z))
      (nabla.cov (bracketField X Y) Z)
  have h' := congrArg (fun s : SmoothVectorField I M => s p) h
  simp only [SmoothVectorField.add_apply] at h'
  rw [nabla.cov_sub_right U (nabla.cov Y (nabla.cov X Z))
    (nabla.cov X (nabla.cov Y Z))] at h'
  exact h'

/-! ### The operator-level second Bianchi identity -/

/-- **Math.** The **covariant derivative of the curvature operator**: for a
direction field `U`,
`(∇_U R)(X,Y)Z = ∇_U (R(X,Y)Z) − R(∇_U X, Y)Z − R(X, ∇_U Y)Z − R(X,Y)(∇_U Z)`,
the Leibniz-rule correction of `∇_U` applied to the `(1,3)`-tensor `R` (here
in do Carmo's sign convention, `R = −R_MT`; the covariant derivative commutes
with the global sign). Pairing with the metric recovers the covariant
differential of the `(0,4)`-tensor
(`covariantDifferential4_curvatureForm_apply`).

Blueprint: `claim:curvature-symmetries-bianchi` (proof step 6). -/
def covariantDerivCurvature (nabla : AffineConnection I M)
    (U X Y Z : SmoothVectorField I M) : SmoothVectorField I M :=
  nabla.cov U (nabla.curvature X Y Z) - nabla.curvature (nabla.cov U X) Y Z
    - nabla.curvature X (nabla.cov U Y) Z - nabla.curvature X Y (nabla.cov U Z)

/-- **Math.** The **second Bianchi identity at the operator level**: for a
symmetric (torsion-free) connection, the cyclic sum of the covariant
derivative of the curvature operator over `(X, Y, U)` vanishes,
`(∇_U R)(X,Y)Z + (∇_X R)(Y,U)Z + (∇_Y R)(U,X)Z = 0`.
Stated for do Carmo's sign convention `R = −R_MT`; since the identity asserts
the vanishing of a cyclic sum, it is convention-independent.

The proof is the invariant version of the blueprint's normal-coordinate
computation: expanding all terms, the twelve triple-covariant-derivative
terms cancel pairwise between `∇_U(R(X,Y)Z)` and `R(X,Y)(∇_U Z)`; the
leftover bracket terms `∇_U ∇_{[X,Y]} Z − ∇_{[X,Y]} ∇_U Z` recombine into
`R([X,Y],U)Z` plus `∇_{[[X,Y],U]} Z`; the double-bracket terms vanish by the
**Jacobi identity** (`Riemannian.DCLieBracket_jacobi_cyclic`); and the
curvature-of-bracket terms cancel against `R(∇_U X, Y)Z + R(X, ∇_U Y)Z` using
**torsion-freeness** `[X,Y] = ∇_X Y − ∇_Y X` and the antisymmetry
`R(A,B) = −R(B,A)`.

Blueprint: `claim:curvature-symmetries-bianchi` (proof step 6). -/
theorem covariantDerivCurvature_cyclic (nabla : AffineConnection I M)
    (hsym : nabla.IsSymmetric) (X Y U Z : SmoothVectorField I M) (p : M) :
    (covariantDerivCurvature nabla U X Y Z) p + (covariantDerivCurvature nabla X Y U Z) p
      + (covariantDerivCurvature nabla Y U X Z) p = 0 := by
  -- torsion-freeness as an identity of bundled vector fields
  have symm_field : ∀ A B : SmoothVectorField I M,
      nabla.cov A B - nabla.cov B A = bracketField A B := by
    intro A B; ext q
    simp only [SmoothVectorField.sub_apply, bracketField_apply]
    exact hsym A B q
  -- expansions of the three `∇_a (R(b,c)Z)` terms
  have hE1 := cov_curvature_apply nabla U X Y Z p
  have hE2 := cov_curvature_apply nabla X Y U Z p
  have hE3 := cov_curvature_apply nabla Y U X Z p
  -- expansions of the three `R(b,c)(∇_a Z)` terms
  have hF1 := nabla.curvature_apply X Y (nabla.cov U Z) p
  have hF2 := nabla.curvature_apply Y U (nabla.cov X Z) p
  have hF3 := nabla.curvature_apply U X (nabla.cov Y Z) p
  -- expansions of the three `R([b,c], a)Z` terms
  have hC1 := nabla.curvature_apply (bracketField X Y) U Z p
  have hC2 := nabla.curvature_apply (bracketField Y U) X Z p
  have hC3 := nabla.curvature_apply (bracketField U X) Y Z p
  -- the double-bracket fields sum to zero (Jacobi identity)
  have hzero : bracketField (bracketField X Y) U + bracketField (bracketField Y U) X
      + bracketField (bracketField U X) Y = (0 : SmoothVectorField I M) := by
    ext q
    simp only [SmoothVectorField.add_apply, bracketField_apply,
      SmoothVectorField.zero_apply]
    exact DCLieBracket_jacobi_cyclic X Y U q
  -- hence so do their covariant derivatives
  have hJ : (nabla.cov (bracketField (bracketField X Y) U) Z) p
      + (nabla.cov (bracketField (bracketField Y U) X) Z) p
      + (nabla.cov (bracketField (bracketField U X) Y) Z) p = 0 := by
    have h : nabla.cov (bracketField (bracketField X Y) U
          + bracketField (bracketField Y U) X + bracketField (bracketField U X) Y) Z
        = nabla.cov (bracketField (bracketField X Y) U) Z
          + nabla.cov (bracketField (bracketField Y U) X) Z
          + nabla.cov (bracketField (bracketField U X) Y) Z := by
      rw [nabla.add_left, nabla.add_left]
    rw [hzero] at h
    have h' := congrArg (fun s : SmoothVectorField I M => s p) h
    simp only [SmoothVectorField.add_apply] at h'
    rw [nabla.cov_zero_left Z p] at h'
    linear_combination (norm := module) -h'
  -- torsion-freeness splits each `R([b,c], a)Z`
  have hT1 : (nabla.curvature (bracketField X Y) U Z) p
      = (nabla.curvature (nabla.cov X Y) U Z) p
        - (nabla.curvature (nabla.cov Y X) U Z) p := by
    rw [← symm_field X Y]
    exact curvature_sub_left nabla (nabla.cov X Y) (nabla.cov Y X) U Z p
  have hT2 : (nabla.curvature (bracketField Y U) X Z) p
      = (nabla.curvature (nabla.cov Y U) X Z) p
        - (nabla.curvature (nabla.cov U Y) X Z) p := by
    rw [← symm_field Y U]
    exact curvature_sub_left nabla (nabla.cov Y U) (nabla.cov U Y) X Z p
  have hT3 : (nabla.curvature (bracketField U X) Y Z) p
      = (nabla.curvature (nabla.cov U X) Y Z) p
        - (nabla.curvature (nabla.cov X U) Y Z) p := by
    rw [← symm_field U X]
    exact curvature_sub_left nabla (nabla.cov U X) (nabla.cov X U) Y Z p
  -- antisymmetry pairs off the leftovers
  have hA1 := nabla.curvature_antisymm_left (nabla.cov Y X) U Z p
  have hA2 := nabla.curvature_antisymm_left (nabla.cov U Y) X Z p
  have hA3 := nabla.curvature_antisymm_left (nabla.cov X U) Y Z p
  simp only [covariantDerivCurvature, SmoothVectorField.sub_apply]
  linear_combination (norm := module) hE1 + hE2 + hE3 - hF1 - hF2 - hF3
    - hC1 - hC2 - hC3 + hT1 + hT2 + hT3 - hA1 - hA2 - hA3 - hJ

/-! ### Pairing with the metric -/

variable [I.Boundaryless]

omit [I.Boundaryless] in
/-- **Math.** For a metric-compatible connection, the covariant differential
of the curvature `(0,4)`-tensor is the metric pairing of the covariant
derivative of the curvature operator:
`∇R(X,Y,Z,W; U) = g((∇_U R)(X,Y)Z, W)`.
This is the blueprint's remark that `∇g = 0` lets covariant differentiation
commute with lowering the index: metric compatibility converts the
directional-derivative term `U(g(R(X,Y)Z, W))` into
`g(∇_U(R(X,Y)Z), W) + g(R(X,Y)Z, ∇_U W)`, and the second summand cancels the
last correction slot of `covariantDifferential4`.

Blueprint: `claim:curvature-symmetries-bianchi` (proof step 6). -/
theorem covariantDifferential4_curvatureForm_apply (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hcompat : nabla.IsMetricCompatible g)
    (X Y Z W U : SmoothVectorField I M) (p : M) :
    covariantDifferential4 nabla (nabla.curvatureForm g) X Y Z W U p
      = g.metricInner p ((covariantDerivCurvature nabla U X Y Z) p) (W p) := by
  have hc : U.dir (nabla.curvatureForm g X Y Z W) p
      = g.metricInner p ((nabla.cov U (nabla.curvature X Y Z)) p) (W p)
        + g.metricInner p ((nabla.curvature X Y Z) p) ((nabla.cov U W) p) :=
    hcompat U (nabla.curvature X Y Z) W p
  simp only [covariantDifferential4, covariantDerivCurvature,
    SmoothVectorField.sub_apply, Riemannian.AffineConnection.curvatureForm,
    RiemannianMetric.metricInner_sub_left]
  rw [hc]
  ring

omit [I.Boundaryless] in
/-- **Math.** The second Bianchi identity, cyclic over the **first two slots
and the differentiation slot**: for a Levi-Civita connection,
`∇R(X,Y,Z,W; U) + ∇R(Y,U,Z,W; X) + ∇R(U,X,Z,W; Y) = 0`.
This is the metric pairing of the operator-level identity
(`covariantDerivCurvature_cyclic`); in Morgan–Tian's index notation it reads
`R_{ijkl,h} + R_{jhkl,i} + R_{hikl,j} = 0`.

Blueprint: `claim:curvature-symmetries-bianchi` (proof step 6). -/
theorem covariantDifferential4_curvatureForm_cyclic_first_pair
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hsym : nabla.IsSymmetric) (hcompat : nabla.IsMetricCompatible g)
    (X Y Z W U : SmoothVectorField I M) (p : M) :
    covariantDifferential4 nabla (nabla.curvatureForm g) X Y Z W U p
      + covariantDifferential4 nabla (nabla.curvatureForm g) Y U Z W X p
      + covariantDifferential4 nabla (nabla.curvatureForm g) U X Z W Y p = 0 := by
  rw [covariantDifferential4_curvatureForm_apply g nabla hcompat X Y Z W U p,
    covariantDifferential4_curvatureForm_apply g nabla hcompat Y U Z W X p,
    covariantDifferential4_curvatureForm_apply g nabla hcompat U X Z W Y p,
    ← RiemannianMetric.metricInner_add_left, ← RiemannianMetric.metricInner_add_left,
    covariantDerivCurvature_cyclic nabla hsym X Y U Z p,
    RiemannianMetric.metricInner_zero_left]

/-- **Math.** The pair-swap symmetry `R(X,Y,Z,W) = R(Z,W,X,Y)` is inherited by
the covariant differential of the curvature `(0,4)`-tensor:
`∇R(X,Y,Z,W; U) = ∇R(Z,W,X,Y; U)`. This is the blueprint's remark that the
first-order symmetries of `R` are preserved by covariant differentiation
(differentiate the identity and use `∇g = 0`); here it follows slotwise from
`Riemannian.AffineConnection.curvatureForm_pairSwap` since every term of
`covariantDifferential4` is an evaluation of the undifferentiated tensor.

Blueprint: `claim:curvature-symmetries-bianchi` (proof step 6). -/
theorem covariantDifferential4_curvatureForm_pairSwap (g : RiemannianMetric I M)
    (nabla : AffineConnection I M)
    (hsym : nabla.IsSymmetric) (hcompat : nabla.IsMetricCompatible g)
    (X Y Z W U : SmoothVectorField I M) (p : M) :
    covariantDifferential4 nabla (nabla.curvatureForm g) X Y Z W U p
      = covariantDifferential4 nabla (nabla.curvatureForm g) Z W X Y U p := by
  have hfun : nabla.curvatureForm g X Y Z W = nabla.curvatureForm g Z W X Y :=
    funext fun q => nabla.curvatureForm_pairSwap g hsym hcompat X Y Z W q
  simp only [covariantDifferential4]
  rw [hfun,
    nabla.curvatureForm_pairSwap g hsym hcompat (nabla.cov U X) Y Z W p,
    nabla.curvatureForm_pairSwap g hsym hcompat X (nabla.cov U Y) Z W p,
    nabla.curvatureForm_pairSwap g hsym hcompat X Y (nabla.cov U Z) W p,
    nabla.curvatureForm_pairSwap g hsym hcompat X Y Z (nabla.cov U W) p]
  ring

/-! ### The second Bianchi identity -/

/-- **Math.** The **second Bianchi identity** for the curvature
`(0,4)`-tensor of a Levi-Civita connection, cyclic over the **third slot, the
fourth slot and the differentiation slot**:
`∇R(X,Y,Z,W; U) + ∇R(X,Y,W,U; Z) + ∇R(X,Y,U,Z; W) = 0`.

In Morgan–Tian's index notation this is exactly
`R_{ijkl,h} + R_{ijlh,k} + R_{ijhk,l} = 0`, cyclic in `(k,l,h)`, under the
dictionary `R_{ijkl} = nabla.curvatureForm g ∂_i ∂_j ∂_k ∂_l` (Morgan–Tian's
`(0,4)`-tensor `g(R_MT(∂_i,∂_j)∂_l, ∂_k)` agrees slotwise with OpenGALib's
`g(R_dC(∂_i,∂_j)∂_k, ∂_l)` — the operator sign flip and the last-two-slot
transposition cancel, see `MorganTianLib.curvatureForm_eq`) and
`R_{ijkl,h} = covariantDifferential4 nabla (nabla.curvatureForm g)
∂_i ∂_j ∂_k ∂_l ∂_h` with the differentiation index `h` in the last slot.

Proof: apply the pair-swap symmetry of `∇R`
(`covariantDifferential4_curvatureForm_pairSwap`) to each summand, turning
the cyclic sum over slots `(3,4,5)` into the cyclic sum over slots `(1,2,5)`,
which is the metric pairing of the operator-level second Bianchi identity
(`covariantDerivCurvature_cyclic`).

Blueprint: `claim:curvature-symmetries-bianchi`. -/
theorem secondBianchi (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) (X Y Z W U : SmoothVectorField I M) (p : M) :
    covariantDifferential4 nabla (nabla.curvatureForm g) X Y Z W U p
      + covariantDifferential4 nabla (nabla.curvatureForm g) X Y W U Z p
      + covariantDifferential4 nabla (nabla.curvatureForm g) X Y U Z W p = 0 := by
  obtain ⟨hsym, hcompat⟩ := hLC
  rw [covariantDifferential4_curvatureForm_pairSwap g nabla hsym hcompat X Y Z W U p,
    covariantDifferential4_curvatureForm_pairSwap g nabla hsym hcompat X Y W U Z p,
    covariantDifferential4_curvatureForm_pairSwap g nabla hsym hcompat X Y U Z W p]
  exact covariantDifferential4_curvatureForm_cyclic_first_pair g nabla hsym hcompat
    Z W X Y U p

end MorganTianLib
