import PoincareLib.Ch01.RicciFrame
import PoincareLib.Ch01.SecondBianchi

/-!
# Morgan–Tian Ch. 1, §1.2 — `dR = 2 div Ric` (divergence of Ricci)

Morgan–Tian's Lemma 1.9 (blueprint `lem:div-ricci-scalar-curvature`): for the
Levi-Civita connection, the differential of the scalar curvature is twice the
divergence of the Ricci tensor,
`dR(U) = 2 (div Ric)(U) = 2 ∑ᵢ (∇_{eᵢ} Ric)(eᵢ, U)`
for any orthonormal basis `{eᵢ}` of the tangent space.

Following the blueprint proof, this is the double metric contraction of the
second Bianchi identity `R_{ijkl,h} + R_{ijlh,k} + R_{ijhk,l} = 0`
(`PoincareLib.secondBianchi`) with `g^{ik} g^{jl}`:
* the first term contracts to `∂_h R` (`dir_scalarCurvatureAt_eq_frame_sum`,
  the frame form of "`g^{ik}g^{jl}R_{ijkl,h} = R_{,h}`");
* the second and third terms each contract to `−(div Ric)(∂_h)`, using the
  antisymmetries of `∇R` in the first and second index pairs
  (`covariantDifferential4_curvatureForm_antisymm_left/right`, the
  differentiated symmetries of `ℛ`) and the symmetry of the Ricci tensor.

All contractions are computed against the smooth local orthonormal frame
`orthoFrameField` of `PoincareLib.Ch01.OrthoFrame`; the frame-derivative
corrections cancel by the antisymmetry of the connection coefficients
(`PoincareLib.Ch01.RicciFrame`), which is the blueprint's "contraction with
`g` commutes with covariant differentiation".

Main declarations:
* `covRicci g nabla hLC U X Y` — the covariant derivative of the Ricci tensor
  `(∇_U Ric)(X, Y) = U(Ric(X,Y)) − Ric(∇_U X, Y) − Ric(X, ∇_U Y)`, at the
  smooth-vector-field level;
* `covRicci_eq_frame_sum` — `(∇_U Ric)(X,Y) = ∑ⱼ ∇R(X, Eⱼ, Y, Eⱼ; U)` on the
  frame neighbourhood: covariant differentiation commutes with the Ricci
  trace;
* `covRicciAt g nabla hLC p u v w` — the same as a pointwise tensor
  `(∇_u Ric)(v, w)` of tangent vectors (well defined by
  `covRicci_congr_apply`, the tensoriality of `∇Ric`);
* `divRicciAt g nabla hLC p w` — the **divergence of the Ricci tensor**
  `(div Ric)(w) = ∑ᵢ (∇_{eᵢ} Ric)(eᵢ, w)`, basis-independent
  (`divRicciAt_eq_sum_orthonormalBasis`);
* `dir_scalarCurvature_eq_two_divRicci` — **the divergence lemma**
  `U(R)(p) = 2 (div Ric)(U(p))` — blueprint `lem:div-ricci-scalar-curvature`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.2,
Lemma 1.9. Blueprint: `lem:div-ricci-scalar-curvature`.
-/

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff Bundle

noncomputable section

set_option linter.unusedSectionVars false

namespace PoincareLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Pointwise slot algebra of the Ricci tensor -/

/-- **Math.** The pointwise Ricci tensor is additive in its first slot.
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem ricciAt_add_left (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) (p : M) (v₁ v₂ w : TangentSpace I p) :
    ricciAt g nabla hLC p (v₁ + v₂) w
      = ricciAt g nabla hLC p v₁ w + ricciAt g nabla hLC p v₂ w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact ricciForm_add_left (isAlgCurvatureForm_curvatureFormAt g nabla hLC p) v₁ v₂ w

/-- **Math.** The pointwise Ricci tensor is `ℝ`-homogeneous in its first slot.
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem ricciAt_smul_left (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) (p : M) (c : ℝ) (v w : TangentSpace I p) :
    ricciAt g nabla hLC p (c • v) w = c * ricciAt g nabla hLC p v w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact ricciForm_smul_left (isAlgCurvatureForm_curvatureFormAt g nabla hLC p) c v w

/-- **Math.** The pointwise Ricci tensor is additive in its second slot.
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem ricciAt_add_right (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) (p : M) (v w₁ w₂ : TangentSpace I p) :
    ricciAt g nabla hLC p v (w₁ + w₂)
      = ricciAt g nabla hLC p v w₁ + ricciAt g nabla hLC p v w₂ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact ricciForm_add_right (isAlgCurvatureForm_curvatureFormAt g nabla hLC p) v w₁ w₂

/-- **Math.** The pointwise Ricci tensor is `ℝ`-homogeneous in its second slot.
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem ricciAt_smul_right (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) (p : M) (c : ℝ) (v w : TangentSpace I p) :
    ricciAt g nabla hLC p v (c • w) = c * ricciAt g nabla hLC p v w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact ricciForm_smul_right (isAlgCurvatureForm_curvatureFormAt g nabla hLC p) c v w

/-! ### The covariant derivative of the Ricci tensor -/

/-- **Math.** The **covariant derivative of the Ricci tensor** along `U`,
`(∇_U Ric)(X, Y) = U(Ric(X,Y)) − Ric(∇_U X, Y) − Ric(X, ∇_U Y)`,
the order-3 covariant tensor obtained from the Ricci `(0,2)`-tensor by the
Leibniz correction (do Carmo Ch. 4 Def. 5.7 pattern, cf.
`covariantDifferential4`). In Morgan–Tian's index notation this is
`Ric_{ab,c}` with `(X, Y; U) = (∂_a, ∂_b; ∂_c)`.
Blueprint: `lem:div-ricci-scalar-curvature`. -/
def covRicci (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) (U X Y : SmoothVectorField I M) : M → ℝ :=
  fun p => U.dir (ricciField g nabla hLC X Y) p
    - ricciField g nabla hLC (nabla.cov U X) Y p
    - ricciField g nabla hLC X (nabla.cov U Y) p

/-- **Math.** **Covariant differentiation commutes with the Ricci trace**: on
the orthonormality neighbourhood of the frame at `α`,
`(∇_U Ric)(X,Y)(q) = ∑ⱼ ∇R(X, Eⱼ, Y, Eⱼ; U)(q)`.
Expanding both sides, the difference consists of the frame-derivative
corrections `ℛ(X, ∇_U Eⱼ, Y, Eⱼ) + ℛ(X, Eⱼ, Y, ∇_U Eⱼ)`, which cancel by
`sum_curvature_cov_corrections_snd_fth`. This is the blueprint's
"since `∇g = 0`, contraction with `g` commutes with covariant
differentiation" for the Ricci contraction.
Blueprint: `lem:div-ricci-scalar-curvature`. -/
theorem covRicci_eq_frame_sum (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) (α : M) {q : M}
    (hq : q ∈ orthoFrameSet (I := I) (M := M) α) (U X Y : SmoothVectorField I M) :
    covRicci g nabla hLC U X Y q
      = ∑ j, covariantDifferential4 nabla (nabla.curvatureForm g) X
          (orthoFrameField g α j) Y (orthoFrameField g α j) U q := by
  classical
  -- the directional-derivative term through the frame representation
  have hrep : ricciField g nabla hLC X Y =ᶠ[𝓝 q]
      fun q' => ∑ j, nabla.curvatureForm g X (orthoFrameField g α j) Y
        (orthoFrameField g α j) q' := by
    filter_upwards [(isOpen_orthoFrameSet (I := I) (M := M) α).mem_nhds hq] with q' hq'
    exact ricciField_eq_frame_sum g nabla hLC α hq' X Y
  have hdir : U.dir (ricciField g nabla hLC X Y) q
      = ∑ j, U.dir (nabla.curvatureForm g X (orthoFrameField g α j) Y
          (orthoFrameField g α j)) q := by
    rw [dir_congr_nhds U hrep]
    exact dir_finset_sum U Finset.univ q fun j _ =>
      curvatureForm_mdifferentiableAt g nabla X (orthoFrameField g α j) Y
        (orthoFrameField g α j) q
  have h2 : ricciField g nabla hLC (nabla.cov U X) Y q
      = ∑ j, nabla.curvatureForm g (nabla.cov U X) (orthoFrameField g α j) Y
          (orthoFrameField g α j) q :=
    ricciField_eq_frame_sum g nabla hLC α hq (nabla.cov U X) Y
  have h3 : ricciField g nabla hLC X (nabla.cov U Y) q
      = ∑ j, nabla.curvatureForm g X (orthoFrameField g α j) (nabla.cov U Y)
          (orthoFrameField g α j) q :=
    ricciField_eq_frame_sum g nabla hLC α hq X (nabla.cov U Y)
  have hcorr := sum_curvature_cov_corrections_snd_fth g nabla hLC α hq X Y U
  -- expand `covariantDifferential4` and split the sums
  have hsplit : ∑ j, covariantDifferential4 nabla (nabla.curvatureForm g) X
      (orthoFrameField g α j) Y (orthoFrameField g α j) U q
      = (∑ j, U.dir (nabla.curvatureForm g X (orthoFrameField g α j) Y
            (orthoFrameField g α j)) q)
        - (∑ j, nabla.curvatureForm g (nabla.cov U X) (orthoFrameField g α j) Y
            (orthoFrameField g α j) q)
        - (∑ j, (nabla.curvatureForm g X (nabla.cov U (orthoFrameField g α j)) Y
              (orthoFrameField g α j) q
            + nabla.curvatureForm g X (orthoFrameField g α j) Y
                (nabla.cov U (orthoFrameField g α j)) q))
        - (∑ j, nabla.curvatureForm g X (orthoFrameField g α j) (nabla.cov U Y)
            (orthoFrameField g α j) q) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [covariantDifferential4]
    ring
  rw [hsplit, hcorr]
  simp only [covRicci, hdir, h2, h3]
  ring

/-! ### The differentiated curvature symmetries -/

/-- **Math.** The antisymmetry of `ℛ` in its **second pair** survives
covariant differentiation: `∇R(X,Y,Z,W;U) = −∇R(X,Y,W,Z;U)`. Differentiating
the identity `ℛ(X,Y,Z,W) = −ℛ(X,Y,W,Z)` term by term (the blueprint's
"covariant differentiation commutes with such permutations of the
arguments"). Blueprint: `lem:div-ricci-scalar-curvature`. -/
theorem covariantDifferential4_curvatureForm_antisymm_right
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) (X Y Z W U : SmoothVectorField I M) (p : M) :
    covariantDifferential4 nabla (nabla.curvatureForm g) X Y Z W U p
      = -covariantDifferential4 nabla (nabla.curvatureForm g) X Y W Z U p := by
  have hfun : ∀ A B C D : SmoothVectorField I M,
      nabla.curvatureForm g A B C D = fun q => -(nabla.curvatureForm g A B D C q) :=
    fun A B C D => funext fun q => nabla.curvatureForm_antisymm_right g hLC.2 A B C D q
  have hdir : U.dir (nabla.curvatureForm g X Y Z W) p
      = -U.dir (nabla.curvatureForm g X Y W Z) p := by
    rw [hfun X Y Z W]
    simp only [SmoothVectorField.dir]
    rw [show (fun q => -(nabla.curvatureForm g X Y W Z q))
      = -(nabla.curvatureForm g X Y W Z) from rfl, mfderiv_neg]
    rfl
  simp only [covariantDifferential4]
  rw [hdir, nabla.curvatureForm_antisymm_right g hLC.2 (nabla.cov U X) Y Z W p,
    nabla.curvatureForm_antisymm_right g hLC.2 X (nabla.cov U Y) Z W p,
    nabla.curvatureForm_antisymm_right g hLC.2 X Y (nabla.cov U Z) W p,
    nabla.curvatureForm_antisymm_right g hLC.2 X Y Z (nabla.cov U W) p]
  ring

/-- **Math.** The antisymmetry of `ℛ` in its **first pair** survives covariant
differentiation: `∇R(X,Y,Z,W;U) = −∇R(Y,X,Z,W;U)`.
Blueprint: `lem:div-ricci-scalar-curvature`. -/
theorem covariantDifferential4_curvatureForm_antisymm_left
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (X Y Z W U : SmoothVectorField I M) (p : M) :
    covariantDifferential4 nabla (nabla.curvatureForm g) X Y Z W U p
      = -covariantDifferential4 nabla (nabla.curvatureForm g) Y X Z W U p := by
  have hfun : ∀ A B C D : SmoothVectorField I M,
      nabla.curvatureForm g A B C D = fun q => -(nabla.curvatureForm g B A C D q) :=
    fun A B C D => funext fun q => nabla.curvatureForm_antisymm_left g A B C D q
  have hdir : U.dir (nabla.curvatureForm g X Y Z W) p
      = -U.dir (nabla.curvatureForm g Y X Z W) p := by
    rw [hfun X Y Z W]
    simp only [SmoothVectorField.dir]
    rw [show (fun q => -(nabla.curvatureForm g Y X Z W q))
      = -(nabla.curvatureForm g Y X Z W) from rfl, mfderiv_neg]
    rfl
  simp only [covariantDifferential4]
  rw [hdir, nabla.curvatureForm_antisymm_left g (nabla.cov U X) Y Z W p,
    nabla.curvatureForm_antisymm_left g X (nabla.cov U Y) Z W p,
    nabla.curvatureForm_antisymm_left g X Y (nabla.cov U Z) W p,
    nabla.curvatureForm_antisymm_left g X Y Z (nabla.cov U W) p]
  ring

/-! ### The scalar contraction -/

/-- **Math.** Splitting a double sum of pointwise sums.
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem double_sum_add {n : ℕ} (f h : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, (f i j + h i j) = (∑ i, ∑ j, f i j) + ∑ i, ∑ j, h i j := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib

/-- **Math.** Pulling a negation out of a double sum.
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem double_sum_neg {n : ℕ} (f : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, -(f i j) = -(∑ i, ∑ j, f i j) := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_neg_distrib (f i)

/-- **Math.** **The scalar-curvature contraction of `∇R`**: at any `p`,
`U(R)(p) = ∑ᵢ∑ⱼ ∇R(Eᵢ, Eⱼ, Eᵢ, Eⱼ; U)(p)` against the orthonormal frame
centred at `p`. This is the blueprint's first contraction
`g^{ik}g^{jl} R_{ijkl,h} = R_{,h}`: the directional derivative of the scalar
curvature is computed through the frame representation, and all
frame-derivative corrections cancel
(`sum_curvature_cov_corrections_fst_trd/_snd_fth_diag`).
Blueprint: `lem:div-ricci-scalar-curvature`. -/
theorem dir_scalarCurvatureAt_eq_frame_sum (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g)
    (U : SmoothVectorField I M) (p : M) :
    U.dir (scalarCurvatureAt g nabla hLC) p
      = ∑ i, ∑ j, covariantDifferential4 nabla (nabla.curvatureForm g)
          (orthoFrameField g p i) (orthoFrameField g p j) (orthoFrameField g p i)
          (orthoFrameField g p j) U p := by
  classical
  have hp := mem_orthoFrameSet_self (I := I) (M := M) p
  -- the directional derivative through the frame representation
  have hrep : scalarCurvatureAt g nabla hLC =ᶠ[𝓝 p]
      fun q => ∑ i, ∑ j, nabla.curvatureForm g (orthoFrameField g p i)
        (orthoFrameField g p j) (orthoFrameField g p i) (orthoFrameField g p j) q := by
    filter_upwards [(isOpen_orthoFrameSet (I := I) (M := M) p).mem_nhds hp] with q hq
    exact scalarCurvatureAt_eq_frame_sum g nabla hLC p hq
  have hdir : U.dir (scalarCurvatureAt g nabla hLC) p
      = ∑ i, ∑ j, U.dir (nabla.curvatureForm g (orthoFrameField g p i)
          (orthoFrameField g p j) (orthoFrameField g p i) (orthoFrameField g p j)) p := by
    rw [dir_congr_nhds U hrep]
    rw [dir_finset_sum U Finset.univ p fun i _ =>
      mdifferentiableAt_finset_sum Finset.univ fun j _ =>
        curvatureForm_mdifferentiableAt g nabla _ _ _ _ p]
    exact Finset.sum_congr rfl fun i _ =>
      dir_finset_sum U Finset.univ p fun j _ =>
        curvatureForm_mdifferentiableAt g nabla _ _ _ _ p
  -- per-term expansion of `∇R` into the derivative minus the four corrections
  have hperterm : ∀ i j, U.dir (nabla.curvatureForm g (orthoFrameField g p i)
      (orthoFrameField g p j) (orthoFrameField g p i) (orthoFrameField g p j)) p
      = covariantDifferential4 nabla (nabla.curvatureForm g) (orthoFrameField g p i)
          (orthoFrameField g p j) (orthoFrameField g p i) (orthoFrameField g p j) U p
        + ((nabla.curvatureForm g (nabla.cov U (orthoFrameField g p i))
              (orthoFrameField g p j) (orthoFrameField g p i) (orthoFrameField g p j) p
            + nabla.curvatureForm g (orthoFrameField g p i) (orthoFrameField g p j)
                (nabla.cov U (orthoFrameField g p i)) (orthoFrameField g p j) p)
          + (nabla.curvatureForm g (orthoFrameField g p i)
              (nabla.cov U (orthoFrameField g p j)) (orthoFrameField g p i)
              (orthoFrameField g p j) p
            + nabla.curvatureForm g (orthoFrameField g p i) (orthoFrameField g p j)
                (orthoFrameField g p i) (nabla.cov U (orthoFrameField g p j)) p)) := by
    intro i j
    simp only [covariantDifferential4]
    ring
  rw [hdir]
  have hsum : ∑ i, ∑ j, U.dir (nabla.curvatureForm g (orthoFrameField g p i)
      (orthoFrameField g p j) (orthoFrameField g p i) (orthoFrameField g p j)) p
      = (∑ i, ∑ j, covariantDifferential4 nabla (nabla.curvatureForm g)
          (orthoFrameField g p i) (orthoFrameField g p j) (orthoFrameField g p i)
          (orthoFrameField g p j) U p)
        + ((∑ i, ∑ j, (nabla.curvatureForm g (nabla.cov U (orthoFrameField g p i))
              (orthoFrameField g p j) (orthoFrameField g p i) (orthoFrameField g p j) p
            + nabla.curvatureForm g (orthoFrameField g p i) (orthoFrameField g p j)
                (nabla.cov U (orthoFrameField g p i)) (orthoFrameField g p j) p))
          + ∑ i, ∑ j, (nabla.curvatureForm g (orthoFrameField g p i)
              (nabla.cov U (orthoFrameField g p j)) (orthoFrameField g p i)
              (orthoFrameField g p j) p
            + nabla.curvatureForm g (orthoFrameField g p i) (orthoFrameField g p j)
                (orthoFrameField g p i) (nabla.cov U (orthoFrameField g p j)) p)) := by
    rw [← double_sum_add, ← double_sum_add]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hperterm i j
  rw [hsum, sum_curvature_cov_corrections_fst_trd g nabla hLC p hp U,
    sum_curvature_cov_corrections_snd_fth_diag g nabla hLC p hp U]
  ring

/-- **Math.** **The frame form of the divergence lemma**:
`U(R)(p) = 2 ∑ᵢ (∇_{Eᵢ} Ric)(Eᵢ, U)(p)` against the orthonormal frame centred
at `p`. This is the double contraction of the second Bianchi identity: for
each `(i,j)`, `secondBianchi` gives
`∇R(Eᵢ,Eⱼ,Eᵢ,Eⱼ;U) + ∇R(Eᵢ,Eⱼ,Eⱼ,U;Eᵢ) + ∇R(Eᵢ,Eⱼ,U,Eᵢ;Eⱼ) = 0`;
summing over `i, j`, the first term is `U(R)`
(`dir_scalarCurvatureAt_eq_frame_sum`), and the other two each contract to
`−∑ᵢ (∇_{Eᵢ} Ric)(Eᵢ, U)` via the differentiated antisymmetries and
(for the third) the pair-relabelling `i ↔ j`.
Blueprint: `lem:div-ricci-scalar-curvature`. -/
theorem dir_scalarCurvatureAt_eq_two_frame_covRicci (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g)
    (U : SmoothVectorField I M) (p : M) :
    U.dir (scalarCurvatureAt g nabla hLC) p
      = 2 * ∑ i, covRicci g nabla hLC (orthoFrameField g p i)
          (orthoFrameField g p i) U p := by
  classical
  have hp := mem_orthoFrameSet_self (I := I) (M := M) p
  -- the three contracted Bianchi terms
  have hBianchi : ∀ i j : Fin (Module.finrank ℝ E),
      covariantDifferential4 nabla (nabla.curvatureForm g) (orthoFrameField g p i)
          (orthoFrameField g p j) (orthoFrameField g p i) (orthoFrameField g p j) U p
        + covariantDifferential4 nabla (nabla.curvatureForm g) (orthoFrameField g p i)
            (orthoFrameField g p j) (orthoFrameField g p j) U (orthoFrameField g p i) p
        + covariantDifferential4 nabla (nabla.curvatureForm g) (orthoFrameField g p i)
            (orthoFrameField g p j) U (orthoFrameField g p i) (orthoFrameField g p j) p
        = 0 :=
    fun i j => secondBianchi g nabla hLC (orthoFrameField g p i) (orthoFrameField g p j)
      (orthoFrameField g p i) (orthoFrameField g p j) U p
  -- second term: antisymmetry in the second pair
  have hT2 : ∀ i j : Fin (Module.finrank ℝ E),
      covariantDifferential4 nabla (nabla.curvatureForm g) (orthoFrameField g p i)
          (orthoFrameField g p j) (orthoFrameField g p j) U (orthoFrameField g p i) p
        = -covariantDifferential4 nabla (nabla.curvatureForm g) (orthoFrameField g p i)
            (orthoFrameField g p j) U (orthoFrameField g p j) (orthoFrameField g p i) p :=
    fun i j => covariantDifferential4_curvatureForm_antisymm_right g nabla hLC
      (orthoFrameField g p i) (orthoFrameField g p j) (orthoFrameField g p j) U
      (orthoFrameField g p i) p
  -- third term: antisymmetry in the first pair
  have hT3 : ∀ i j : Fin (Module.finrank ℝ E),
      covariantDifferential4 nabla (nabla.curvatureForm g) (orthoFrameField g p i)
          (orthoFrameField g p j) U (orthoFrameField g p i) (orthoFrameField g p j) p
        = -covariantDifferential4 nabla (nabla.curvatureForm g) (orthoFrameField g p j)
            (orthoFrameField g p i) U (orthoFrameField g p i) (orthoFrameField g p j) p :=
    fun i j => covariantDifferential4_curvatureForm_antisymm_left g nabla
      (orthoFrameField g p i) (orthoFrameField g p j) U (orthoFrameField g p i)
      (orthoFrameField g p j) p
  -- name the divergence-shaped double sum
  set C : ℝ := ∑ i, ∑ j, covariantDifferential4 nabla (nabla.curvatureForm g)
      (orthoFrameField g p i) (orthoFrameField g p j) U (orthoFrameField g p j)
      (orthoFrameField g p i) p with hC_def
  -- the relabelled third sum equals `C`
  have hswap : ∑ i, ∑ j, covariantDifferential4 nabla (nabla.curvatureForm g)
      (orthoFrameField g p j) (orthoFrameField g p i) U (orthoFrameField g p i)
      (orthoFrameField g p j) p = C := by
    rw [hC_def]
    exact Finset.sum_comm
  -- sum the Bianchi identity over the frame
  have hsum0 : ∑ i, ∑ j, (covariantDifferential4 nabla (nabla.curvatureForm g)
      (orthoFrameField g p i) (orthoFrameField g p j) (orthoFrameField g p i)
      (orthoFrameField g p j) U p
    + covariantDifferential4 nabla (nabla.curvatureForm g) (orthoFrameField g p i)
        (orthoFrameField g p j) (orthoFrameField g p j) U (orthoFrameField g p i) p
    + covariantDifferential4 nabla (nabla.curvatureForm g) (orthoFrameField g p i)
        (orthoFrameField g p j) U (orthoFrameField g p i) (orthoFrameField g p j) p)
      = (0 : ℝ) :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => hBianchi i j
  -- the second contracted term sums to `-C`
  have hT2sum : ∑ i, ∑ j, covariantDifferential4 nabla (nabla.curvatureForm g)
      (orthoFrameField g p i) (orthoFrameField g p j) (orthoFrameField g p j) U
      (orthoFrameField g p i) p = -C := by
    calc ∑ i, ∑ j, covariantDifferential4 nabla (nabla.curvatureForm g)
              (orthoFrameField g p i) (orthoFrameField g p j) (orthoFrameField g p j) U
              (orthoFrameField g p i) p
        = ∑ i, ∑ j, -(covariantDifferential4 nabla (nabla.curvatureForm g)
            (orthoFrameField g p i) (orthoFrameField g p j) U (orthoFrameField g p j)
            (orthoFrameField g p i) p) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hT2 i j
      _ = -C := by rw [double_sum_neg, hC_def]
  -- the third contracted term sums to `-C` after relabelling `i ↔ j`
  have hT3sum : ∑ i, ∑ j, covariantDifferential4 nabla (nabla.curvatureForm g)
      (orthoFrameField g p i) (orthoFrameField g p j) U (orthoFrameField g p i)
      (orthoFrameField g p j) p = -C := by
    calc ∑ i, ∑ j, covariantDifferential4 nabla (nabla.curvatureForm g)
              (orthoFrameField g p i) (orthoFrameField g p j) U (orthoFrameField g p i)
              (orthoFrameField g p j) p
        = ∑ i, ∑ j, -(covariantDifferential4 nabla (nabla.curvatureForm g)
            (orthoFrameField g p j) (orthoFrameField g p i) U (orthoFrameField g p i)
            (orthoFrameField g p j) p) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hT3 i j
      _ = -C := by rw [double_sum_neg, hswap]
  -- split the summed Bianchi identity into the three double sums
  have hsplit : (∑ i, ∑ j, covariantDifferential4 nabla (nabla.curvatureForm g)
        (orthoFrameField g p i) (orthoFrameField g p j) (orthoFrameField g p i)
        (orthoFrameField g p j) U p)
      + (∑ i, ∑ j, covariantDifferential4 nabla (nabla.curvatureForm g)
          (orthoFrameField g p i) (orthoFrameField g p j) (orthoFrameField g p j) U
          (orthoFrameField g p i) p)
      + (∑ i, ∑ j, covariantDifferential4 nabla (nabla.curvatureForm g)
          (orthoFrameField g p i) (orthoFrameField g p j) U (orthoFrameField g p i)
          (orthoFrameField g p j) p) = 0 := by
    rw [← double_sum_add, ← double_sum_add]
    exact hsum0
  rw [hT2sum, hT3sum] at hsplit
  -- assemble
  have hC_covRicci : C = ∑ i, covRicci g nabla hLC (orthoFrameField g p i)
      (orthoFrameField g p i) U p := by
    rw [hC_def]
    exact (Finset.sum_congr rfl fun i _ =>
      (covRicci_eq_frame_sum g nabla hLC p hp (orthoFrameField g p i)
        (orthoFrameField g p i) U)).symm
  rw [dir_scalarCurvatureAt_eq_frame_sum g nabla hLC U p, ← hC_covRicci]
  linarith [hsplit]

/-! ### Tensoriality of `∇Ric` and the pointwise divergence -/

variable (g : RiemannianMetric I M) (nabla : AffineConnection I M)
  (hLC : nabla.IsLeviCivita g)

/-- **Math.** `∇Ric` is additive in the direction slot.
Blueprint: `lem:div-ricci-scalar-curvature` (tensoriality). -/
theorem covRicci_add_dir (U₁ U₂ X Y : SmoothVectorField I M) (q : M) :
    covRicci g nabla hLC (U₁ + U₂) X Y q
      = covRicci g nabla hLC U₁ X Y q + covRicci g nabla hLC U₂ X Y q := by
  simp only [covRicci]
  rw [SmoothVectorField.dir_add_field U₁ U₂ _ q, nabla.add_left U₁ U₂ X,
    nabla.add_left U₁ U₂ Y]
  simp only [ricciField, SmoothVectorField.add_apply, ricciAt_add_left, ricciAt_add_right]
  ring

/-- **Math.** `∇Ric` is `𝒟(M)`-homogeneous in the direction slot.
Blueprint: `lem:div-ricci-scalar-curvature` (tensoriality). -/
theorem covRicci_smul_dir (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (U X Y : SmoothVectorField I M) (q : M) :
    covRicci g nabla hLC (SmoothVectorField.smul f hf U) X Y q
      = f q * covRicci g nabla hLC U X Y q := by
  simp only [covRicci]
  rw [SmoothVectorField.dir_smul_field hf U _ q, nabla.smul_left f hf U X,
    nabla.smul_left f hf U Y]
  simp only [ricciField, SmoothVectorField.smul_apply, ricciAt_smul_left,
    ricciAt_smul_right]
  ring

/-- **Math.** `∇Ric` is additive in its first tensor slot.
Blueprint: `lem:div-ricci-scalar-curvature` (tensoriality). -/
theorem covRicci_add_fst (U X₁ X₂ Y : SmoothVectorField I M) (q : M) :
    covRicci g nabla hLC U (X₁ + X₂) Y q
      = covRicci g nabla hLC U X₁ Y q + covRicci g nabla hLC U X₂ Y q := by
  simp only [covRicci]
  have hfun : ricciField g nabla hLC (X₁ + X₂) Y
      = fun q' => ricciField g nabla hLC X₁ Y q' + ricciField g nabla hLC X₂ Y q' := by
    funext q'
    simp only [ricciField, SmoothVectorField.add_apply, ricciAt_add_left]
  rw [hfun, U.dir_add q (ricciField_mdifferentiableAt g nabla hLC X₁ Y q)
    (ricciField_mdifferentiableAt g nabla hLC X₂ Y q), nabla.add_right U X₁ X₂]
  simp only [ricciField, SmoothVectorField.add_apply, ricciAt_add_left]
  ring

/-- **Math.** `∇Ric` is `𝒟(M)`-homogeneous in its first tensor slot: the
`U(f)`-terms produced by the Leibniz rules of `U.dir` and of `∇_U (fX)`
cancel. This is the tensoriality mechanism of the covariant differential.
Blueprint: `lem:div-ricci-scalar-curvature` (tensoriality). -/
theorem covRicci_smul_fst (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (U X Y : SmoothVectorField I M) (q : M) :
    covRicci g nabla hLC U (SmoothVectorField.smul f hf X) Y q
      = f q * covRicci g nabla hLC U X Y q := by
  simp only [covRicci]
  have hfun : ricciField g nabla hLC (SmoothVectorField.smul f hf X) Y
      = fun q' => f q' * ricciField g nabla hLC X Y q' := by
    funext q'
    simp only [ricciField, SmoothVectorField.smul_apply, ricciAt_smul_left]
  rw [hfun, U.dir_mul q (hf.mdifferentiableAt (by simp))
    (ricciField_mdifferentiableAt g nabla hLC X Y q)]
  have h2 : ricciField g nabla hLC (nabla.cov U (SmoothVectorField.smul f hf X)) Y q
      = f q * ricciField g nabla hLC (nabla.cov U X) Y q
        + U.dir f q * ricciField g nabla hLC X Y q := by
    simp only [ricciField]
    rw [nabla.leibniz f hf U X q, ricciAt_add_left, ricciAt_smul_left, ricciAt_smul_left]
  have h3 : ricciField g nabla hLC (SmoothVectorField.smul f hf X) (nabla.cov U Y) q
      = f q * ricciField g nabla hLC X (nabla.cov U Y) q := by
    simp only [ricciField, SmoothVectorField.smul_apply, ricciAt_smul_left]
  rw [h2, h3]
  ring

/-- **Math.** `∇Ric` is additive in its second tensor slot.
Blueprint: `lem:div-ricci-scalar-curvature` (tensoriality). -/
theorem covRicci_add_snd (U X Y₁ Y₂ : SmoothVectorField I M) (q : M) :
    covRicci g nabla hLC U X (Y₁ + Y₂) q
      = covRicci g nabla hLC U X Y₁ q + covRicci g nabla hLC U X Y₂ q := by
  simp only [covRicci]
  have hfun : ricciField g nabla hLC X (Y₁ + Y₂)
      = fun q' => ricciField g nabla hLC X Y₁ q' + ricciField g nabla hLC X Y₂ q' := by
    funext q'
    simp only [ricciField, SmoothVectorField.add_apply, ricciAt_add_right]
  rw [hfun, U.dir_add q (ricciField_mdifferentiableAt g nabla hLC X Y₁ q)
    (ricciField_mdifferentiableAt g nabla hLC X Y₂ q), nabla.add_right U Y₁ Y₂]
  simp only [ricciField, SmoothVectorField.add_apply, ricciAt_add_right]
  ring

/-- **Math.** `∇Ric` is `𝒟(M)`-homogeneous in its second tensor slot.
Blueprint: `lem:div-ricci-scalar-curvature` (tensoriality). -/
theorem covRicci_smul_snd (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (U X Y : SmoothVectorField I M) (q : M) :
    covRicci g nabla hLC U X (SmoothVectorField.smul f hf Y) q
      = f q * covRicci g nabla hLC U X Y q := by
  simp only [covRicci]
  have hfun : ricciField g nabla hLC X (SmoothVectorField.smul f hf Y)
      = fun q' => f q' * ricciField g nabla hLC X Y q' := by
    funext q'
    simp only [ricciField, SmoothVectorField.smul_apply, ricciAt_smul_right]
  rw [hfun, U.dir_mul q (hf.mdifferentiableAt (by simp))
    (ricciField_mdifferentiableAt g nabla hLC X Y q)]
  have h2 : ricciField g nabla hLC X (nabla.cov U (SmoothVectorField.smul f hf Y)) q
      = f q * ricciField g nabla hLC X (nabla.cov U Y) q
        + U.dir f q * ricciField g nabla hLC X Y q := by
    simp only [ricciField]
    rw [nabla.leibniz f hf U Y q, ricciAt_add_right, ricciAt_smul_right, ricciAt_smul_right]
  have h3 : ricciField g nabla hLC (SmoothVectorField.smul f hf X) Y q
      = f q * ricciField g nabla hLC X Y q := by
    simp only [ricciField, SmoothVectorField.smul_apply, ricciAt_smul_left]
  have h4 : ricciField g nabla hLC (nabla.cov U X) (SmoothVectorField.smul f hf Y) q
      = f q * ricciField g nabla hLC (nabla.cov U X) Y q := by
    simp only [ricciField, SmoothVectorField.smul_apply, ricciAt_smul_right]
  rw [h2, h4]
  ring

/-- **Math.** **Tensoriality of `∇Ric`**: its value at `p` depends only on the
values of the three vector-field arguments at `p`. The direction slot is
pointwise by construction (`mfderiv` and `cov_congr_apply_left`); the two
tensor slots follow from the additivity/homogeneity above through the
bump-function locality engine (`tensorial_congr_apply`).
Blueprint: `lem:div-ricci-scalar-curvature`. -/
theorem covRicci_congr_apply {U U' X X' Y Y' : SmoothVectorField I M} {p : M}
    (hU : U p = U' p) (hX : X p = X' p) (hY : Y p = Y' p) :
    covRicci g nabla hLC U X Y p = covRicci g nabla hLC U' X' Y' p := by
  have h1 : covRicci g nabla hLC U X Y p = covRicci g nabla hLC U' X Y p := by
    simp only [covRicci]
    have hdir : U.dir (ricciField g nabla hLC X Y) p
        = U'.dir (ricciField g nabla hLC X Y) p := by
      simp only [SmoothVectorField.dir]
      exact congrArg _ hU
    have hcX : (nabla.cov U X) p = (nabla.cov U' X) p := nabla.cov_congr_apply_left X hU
    have hcY : (nabla.cov U Y) p = (nabla.cov U' Y) p := nabla.cov_congr_apply_left Y hU
    simp only [ricciField]
    rw [hdir, hcX, hcY]
  have h2 : covRicci g nabla hLC U' X Y p = covRicci g nabla hLC U' X' Y p :=
    tensorial_congr_apply (fun X'' => covRicci g nabla hLC U' X'' Y)
      (fun A B q => covRicci_add_fst g nabla hLC U' A B Y q)
      (fun f hf A q => covRicci_smul_fst g nabla hLC f hf U' A Y q) hX
  have h3 : covRicci g nabla hLC U' X' Y p = covRicci g nabla hLC U' X' Y' p :=
    tensorial_congr_apply (fun Y'' => covRicci g nabla hLC U' X' Y'')
      (fun A B q => covRicci_add_snd g nabla hLC U' X' A B q)
      (fun f hf A q => covRicci_smul_snd g nabla hLC f hf U' X' A q) hY
  rw [h1, h2, h3]

/-- **Math.** The **covariant derivative of the Ricci tensor as a pointwise
tensor**: for tangent vectors `u, v, w ∈ T_pM`,
`covRicciAt g ∇ p u v w = (∇_u Ric)(v, w)`, computed via arbitrary global
extensions (well defined by `covRicci_congr_apply`). In Morgan–Tian's index
notation this is `Ric_{ab,c}` evaluated at `(v, w; u) = (∂_a, ∂_b; ∂_c)`.
Blueprint: `lem:div-ricci-scalar-curvature`. -/
noncomputable def covRicciAt (p : M) (u v w : TangentSpace I p) : ℝ :=
  covRicci g nabla hLC (extendVector p u) (extendVector p v) (extendVector p w) p

/-- **Math.** The pointwise `∇Ric` evaluates vector fields pointwise.
Blueprint: `lem:div-ricci-scalar-curvature`. -/
theorem covRicciAt_eq (U X Y : SmoothVectorField I M) (p : M) :
    covRicciAt g nabla hLC p (U p) (X p) (Y p) = covRicci g nabla hLC U X Y p :=
  covRicci_congr_apply g nabla hLC (extendVector_apply p (U p))
    (extendVector_apply p (X p)) (extendVector_apply p (Y p))

/-- **Math.** `covRicciAt` is additive in the direction slot.
Blueprint: `lem:div-ricci-scalar-curvature`. -/
theorem covRicciAt_add_dir (p : M) (u₁ u₂ v w : TangentSpace I p) :
    covRicciAt g nabla hLC p (u₁ + u₂) v w
      = covRicciAt g nabla hLC p u₁ v w + covRicciAt g nabla hLC p u₂ v w := by
  have h : covRicciAt g nabla hLC p (u₁ + u₂) v w
      = covRicci g nabla hLC (extendVector p u₁ + extendVector p u₂)
          (extendVector p v) (extendVector p w) p :=
    covRicci_congr_apply g nabla hLC (by simp) rfl rfl
  rw [h, covRicci_add_dir]
  rfl

/-- **Math.** `covRicciAt` is `ℝ`-homogeneous in the direction slot.
Blueprint: `lem:div-ricci-scalar-curvature`. -/
theorem covRicciAt_smul_dir (p : M) (c : ℝ) (u v w : TangentSpace I p) :
    covRicciAt g nabla hLC p (c • u) v w = c * covRicciAt g nabla hLC p u v w := by
  have h : covRicciAt g nabla hLC p (c • u) v w
      = covRicci g nabla hLC
          (SmoothVectorField.smul (fun _ => c) contMDiff_const (extendVector p u))
          (extendVector p v) (extendVector p w) p :=
    covRicci_congr_apply g nabla hLC (by simp) rfl rfl
  rw [h, covRicci_smul_dir]
  rfl

/-- **Math.** `covRicciAt` is additive in its first tensor slot.
Blueprint: `lem:div-ricci-scalar-curvature`. -/
theorem covRicciAt_add_fst (p : M) (u v₁ v₂ w : TangentSpace I p) :
    covRicciAt g nabla hLC p u (v₁ + v₂) w
      = covRicciAt g nabla hLC p u v₁ w + covRicciAt g nabla hLC p u v₂ w := by
  have h : covRicciAt g nabla hLC p u (v₁ + v₂) w
      = covRicci g nabla hLC (extendVector p u)
          (extendVector p v₁ + extendVector p v₂) (extendVector p w) p :=
    covRicci_congr_apply g nabla hLC rfl (by simp) rfl
  rw [h, covRicci_add_fst]
  rfl

/-- **Math.** `covRicciAt` is `ℝ`-homogeneous in its first tensor slot.
Blueprint: `lem:div-ricci-scalar-curvature`. -/
theorem covRicciAt_smul_fst (p : M) (c : ℝ) (u v w : TangentSpace I p) :
    covRicciAt g nabla hLC p u (c • v) w = c * covRicciAt g nabla hLC p u v w := by
  have h : covRicciAt g nabla hLC p u (c • v) w
      = covRicci g nabla hLC (extendVector p u)
          (SmoothVectorField.smul (fun _ => c) contMDiff_const (extendVector p v))
          (extendVector p w) p :=
    covRicci_congr_apply g nabla hLC rfl (by simp) rfl
  rw [h, covRicci_smul_fst]
  rfl

/-- **Math.** `(u, v) ↦ (∇_u Ric)(v, w)` as a bilinear map on `T_pM`, the
form whose metric trace is the divergence of the Ricci tensor.
Blueprint: `lem:div-ricci-scalar-curvature`. -/
noncomputable def covRicciBilin (p : M) (w : TangentSpace I p) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => covRicciAt g nabla hLC p u v w)
    (fun u₁ u₂ v => covRicciAt_add_dir g nabla hLC p u₁ u₂ v w)
    (fun c u v => by
      simp only [smul_eq_mul]
      exact covRicciAt_smul_dir g nabla hLC p c u v w)
    (fun u v₁ v₂ => covRicciAt_add_fst g nabla hLC p u v₁ v₂ w)
    (fun c u v => by
      simp only [smul_eq_mul]
      exact covRicciAt_smul_fst g nabla hLC p c u v w)

/-- **Math.** The **divergence of the Ricci tensor** at `p`, evaluated on
`w ∈ T_pM`: `(div Ric)(w) = ∑ᵢ (∇_{eᵢ} Ric)(eᵢ, w)` for an orthonormal basis
`{eᵢ}` of `(T_pM, g_p)` — Morgan–Tian's `div(Ric)(∂_h) = g^{rs} Ric_{hs,r}`.
Defined against `stdOrthonormalBasis`; independent of the basis by
`divRicciAt_eq_sum_orthonormalBasis`.
Blueprint: `lem:div-ricci-scalar-curvature`. -/
noncomputable def divRicciAt (p : M) (w : TangentSpace I p) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ i, covRicciAt g nabla hLC p (stdOrthonormalBasis ℝ (TangentSpace I p) i)
    (stdOrthonormalBasis ℝ (TangentSpace I p) i) w

/-- **Math.** The divergence of the Ricci tensor is the trace of a bilinear
form, hence can be computed against **any** orthonormal basis of
`(T_pM, g_p)`. Blueprint: `lem:div-ricci-scalar-curvature`. -/
theorem divRicciAt_eq_sum_orthonormalBasis (p : M) (w : TangentSpace I p)
    {ι : Type*} [Fintype ι]
    (e : letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace I p)) :
    divRicciAt g nabla hLC p w = ∑ i, covRicciAt g nabla hLC p (e i) (e i) w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := OrthonormalBasis.sum_apply_diagonal_invariant
    (stdOrthonormalBasis ℝ (TangentSpace I p)) e (covRicciBilin g nabla hLC p w)
  have hstd : divRicciAt g nabla hLC p w
      = ∑ i, (covRicciBilin g nabla hLC p w)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) := rfl
  rw [hstd, h]
  simp only [covRicciBilin, LinearMap.mk₂_apply]

/-- **Math.** **The divergence of Ricci from the second Bianchi identity**
(Morgan–Tian Lemma 1.9): for the Levi-Civita connection of a Riemannian
manifold, the differential of the scalar curvature is twice the divergence of
the Ricci tensor:
`U(R)(p) = 2 (div Ric)(U(p))` for every smooth vector field `U` and `p ∈ M` —
`dR = 2 div(Ric) = 2 ∇* Ric`.

This is the double metric contraction of the second Bianchi identity
(`secondBianchi`), computed against the smooth local orthonormal frame at `p`
(`dir_scalarCurvatureAt_eq_two_frame_covRicci`) and rephrased through the
basis-independent divergence `divRicciAt`.
Blueprint: `lem:div-ricci-scalar-curvature`. -/
theorem dir_scalarCurvature_eq_two_divRicci (U : SmoothVectorField I M) (p : M) :
    U.dir (scalarCurvatureAt g nabla hLC) p = 2 * divRicciAt g nabla hLC p (U p) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [dir_scalarCurvatureAt_eq_two_frame_covRicci g nabla hLC U p,
    divRicciAt_eq_sum_orthonormalBasis g nabla hLC p (U p)
      (orthoFrameBasis g p (mem_orthoFrameSet_self (I := I) p))]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [orthoFrameBasis_apply g p (mem_orthoFrameSet_self (I := I) p) i]
  exact (covRicciAt_eq g nabla hLC (orthoFrameField g p i) (orthoFrameField g p i)
    U p).symm

end PoincareLib
