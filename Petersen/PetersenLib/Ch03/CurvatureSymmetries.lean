import PetersenLib.Ch03.CurvatureTensor

/-!
# Petersen Ch. 3, §3.1.1 — Prop. 3.1.1: the symmetries of the curvature tensor

The four symmetries of the Riemannian curvature tensor (Petersen Prop. 3.1.1):

1. skew-symmetry in the first two and the last two entries
   (`curvatureTensorFour_antisymm_left`, `curvatureTensorFour_antisymm_right`);
2. symmetry between the first and the second pair (`curvatureTensorFour_pairSwap`);
3. Bianchi's first identity (`curvatureTensor_firstBianchi`);
4. Bianchi's second identity (`curvatureTensor_secondBianchi`), for the
   covariant derivative `∇R` of the curvature tensor
   (`covariantDerivativeCurvature`).

All four are packaged in the blueprint node `curvatureTensor_symmetries`.

## Proof notes

* (1, second half) follows from `⟨R(X,Y)Z, Z⟩ = 0`
  (`curvatureTensorFour_self_eq_zero`, via metric compatibility) by
  polarization; (2) is the classical combinatorial consequence of (1) and (3).
* (3) regroups the six double covariant derivatives via torsion-freeness into
  nested brackets and closes with the Jacobi identity
  (`lieDerivativeVectorField_jacobi_cyclic`).
* (4) is proved by direct expansion at the level of vector fields: in the
  cyclic sum all twelve triple-derivative terms cancel in pairs, the remaining
  first-order terms regroup by torsion-freeness into bracket terms which cancel
  the `∇_{[·,·]}` contributions, and the leftover
  `∇_{[∇_X Y, Z] + [Z, ∇_Y X] + …} W` term vanishes by the Jacobi identity —
  no coordinates and no pointwise tensoriality are needed.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.1.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]

/-! ## Jacobi identities for the Lie bracket -/

omit [I.Boundaryless] in
/-- The Leibniz (Jacobi) identity for the Lie bracket of smooth vector fields:
`[X, [U, V]] = [[X, U], V] + [U, [X, V]]`, pointwise. -/
theorem lieDerivativeVectorField_leibniz
    {X U V : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hU : IsSmoothVectorField U)
    (hV : IsSmoothVectorField V) (p : M) :
    lieDerivativeVectorField I X (lieDerivativeVectorField I U V) p
      = lieDerivativeVectorField I (lieDerivativeVectorField I X U) V p
        + lieDerivativeVectorField I U (lieDerivativeVectorField I X V) p := by
  haveI : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have h2 : ∀ {W : Π x : M, TangentSpace I x}, IsSmoothVectorField W →
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
        (fun y => (⟨y, W y⟩ : TangentBundle I M)) p := by
    intro W hW
    refine (hW p).of_le ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top
  exact VectorField.leibniz_identity_mlieBracket_apply (h2 hX) (h2 hU) (h2 hV)

/-- The cyclic Jacobi identity `[[X,Y],Z] + [[Y,Z],X] + [[Z,X],Y] = 0`,
pointwise. -/
theorem lieDerivativeVectorField_jacobi_cyclic
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (p : M) :
    lieDerivativeVectorField I (lieDerivativeVectorField I X Y) Z p
      + lieDerivativeVectorField I (lieDerivativeVectorField I Y Z) X p
      + lieDerivativeVectorField I (lieDerivativeVectorField I Z X) Y p = 0 := by
  have hYZ : IsSmoothVectorField (lieDerivativeVectorField I Y Z) :=
    hY.lieDerivativeVectorField hZ
  -- Leibniz: [Z, [X, Y]] = [[Z, X], Y] + [X, [Z, Y]]
  have hleib := lieDerivativeVectorField_leibniz hZ hX hY p
  -- outer swaps
  have s₁ : lieDerivativeVectorField I (lieDerivativeVectorField I X Y) Z p
      = -(lieDerivativeVectorField I Z (lieDerivativeVectorField I X Y) p) :=
    VectorField.mlieBracket_swap_apply
  have s₂ : lieDerivativeVectorField I (lieDerivativeVectorField I Y Z) X p
      = -(lieDerivativeVectorField I X (lieDerivativeVectorField I Y Z) p) :=
    VectorField.mlieBracket_swap_apply
  -- inner swap: [X, [Z, Y]] = −[X, [Y, Z]]
  have s₃ : lieDerivativeVectorField I X (lieDerivativeVectorField I Z Y) p
      = -(lieDerivativeVectorField I X (lieDerivativeVectorField I Y Z) p) := by
    have hd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun q => (⟨q, lieDerivativeVectorField I Y Z q⟩ : TangentBundle I M)) p :=
      (hYZ p).mdifferentiableAt (by decide)
    have e : lieDerivativeVectorField I Z Y
        = (-1 : ℝ) • lieDerivativeVectorField I Y Z := by
      funext q
      rw [Pi.smul_apply, neg_one_smul]
      exact VectorField.mlieBracket_swap_apply
    calc lieDerivativeVectorField I X (lieDerivativeVectorField I Z Y) p
        = VectorField.mlieBracket I X
            ((-1 : ℝ) • lieDerivativeVectorField I Y Z) p := by rw [← e]; rfl
      _ = (-1 : ℝ) • VectorField.mlieBracket I X
            (lieDerivativeVectorField I Y Z) p :=
          VectorField.mlieBracket_const_smul_right hd
      _ = -(lieDerivativeVectorField I X (lieDerivativeVectorField I Y Z) p) := by
          rw [neg_one_smul]; rfl
  rw [s₁, s₂, hleib]
  linear_combination (norm := module) -s₃

omit [I.Boundaryless] in
/-- `[A − B, Z] = [A, Z] − [B, Z]` pointwise, for smooth `A`, `B`. -/
theorem lieDerivativeVectorField_sub_left
    {A B : Π x : M, TangentSpace I x}
    (hA : IsSmoothVectorField A) (hB : IsSmoothVectorField B)
    (Z : Π x : M, TangentSpace I x) (p : M) :
    lieDerivativeVectorField I (fun q => A q - B q) Z p
      = lieDerivativeVectorField I A Z p - lieDerivativeVectorField I B Z p := by
  have hA' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, A q⟩ : TangentBundle I M)) p :=
    (hA p).mdifferentiableAt (by decide)
  have hB' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, B q⟩ : TangentBundle I M)) p :=
    (hB p).mdifferentiableAt (by decide)
  have hB'' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, ((-1 : ℝ) • B) q⟩ : TangentBundle I M)) p :=
    MDifferentiableAt.smul_section mdifferentiableAt_const hB'
  have e : (fun q => A q - B q) = A + (-1 : ℝ) • B := by
    funext q
    simp [sub_eq_add_neg]
  calc lieDerivativeVectorField I (fun q => A q - B q) Z p
      = VectorField.mlieBracket I (A + (-1 : ℝ) • B) Z p := by rw [← e]; rfl
    _ = VectorField.mlieBracket I A Z p
        + VectorField.mlieBracket I ((-1 : ℝ) • B) Z p :=
        VectorField.mlieBracket_add_left hA' hB''
    _ = VectorField.mlieBracket I A Z p
        + (-1 : ℝ) • VectorField.mlieBracket I B Z p := by
        rw [VectorField.mlieBracket_const_smul_left hB']
    _ = lieDerivativeVectorField I A Z p - lieDerivativeVectorField I B Z p := by
        rw [neg_one_smul, ← sub_eq_add_neg]; rfl

/-! ## `⟨R(X,Y)Z, Z⟩ = 0` and skew-symmetry in the last two entries -/

/-- **Math.** Key step for Prop. 3.1.1(1): `⟨R(X,Y)Z, Z⟩ = 0` for the Riemannian
connection. By metric compatibility `⟨∇_W Z, Z⟩ = ½ D_W g(Z,Z)`, so the two
double-derivative terms contribute `½ D_X D_Y g(Z,Z) − ½ D_Y D_X g(Z,Z)`, which
is cancelled by the bracket term `½ D_{[X,Y]} g(Z,Z)`. -/
theorem curvatureTensorFour_self_eq_zero {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (p : M) :
    curvatureTensorFour D X Y Z Z p = 0 := by
  -- the squared-length function f = g(Z, Z) and its smoothness
  have hf : ContMDiff I 𝓘(ℝ) ∞ (fun q => g.metricInner q (Z q) (Z q)) := by
    have h := (metricOperator_isTensorOperator g).smooth_eval ![Z, Z]
      (by intro i; fin_cases i <;> simpa using hZ)
    have e : (metricOperator g ![Z, Z] : M → ℝ)
        = fun q => g.metricInner q (Z q) (Z q) := by
      funext q; simp [metricOperator]
    rwa [e] at h
  -- ⟨∇_W Z, Z⟩ = ½ D_W f, pointwise in the field W
  have hhalf : ∀ (W : Π x : M, TangentSpace I x) (q : M),
      g.metricInner q (D.cov q (W q) Z) (Z q)
        = (1 / 2) * directionalDerivative W
            (fun r => g.metricInner r (Z r) (Z r)) q := by
    intro W q
    have hc := D.metric_compat hZ hZ q (W q)
    rw [dirTangent_eq_directionalDerivative] at hc
    have hcomm : g.metricInner q (Z q) (D.cov q (W q) Z)
        = g.metricInner q (D.cov q (W q) Z) (Z q) := g.metricInner_comm ..
    rw [hcomm] at hc
    linarith [hc]
  -- differentiability of the first directional derivatives
  have hdXf : ContMDiff I 𝓘(ℝ) ∞
      (directionalDerivative X (fun q => g.metricInner q (Z q) (Z q))) :=
    hX.directionalDerivative_contMDiff hf
  have hdYf : ContMDiff I 𝓘(ℝ) ∞
      (directionalDerivative Y (fun q => g.metricInner q (Z q) (Z q))) :=
    hY.directionalDerivative_contMDiff hf
  -- expand ⟨∇_X ∇_Y Z, Z⟩ via metric compatibility and hhalf
  have hI1 : directionalDerivative X
        (fun q => g.metricInner q (D.cov q (Y q) Z) (Z q)) p
      = g.metricInner p
          (D.cov p (X p) (D.toAffineConnection.covField Y Z)) (Z p)
        + g.metricInner p (D.cov p (Y p) Z) (D.cov p (X p) Z) := by
    have h := D.metric_compat (D.smooth_cov hY hZ) hZ p (X p)
    rw [dirTangent_eq_directionalDerivative] at h
    exact h
  have eY : (fun q => g.metricInner q (D.cov q (Y q) Z) (Z q))
      = fun q => (1 / 2) * directionalDerivative Y
          (fun r => g.metricInner r (Z r) (Z r)) q := by
    funext q; exact hhalf Y q
  rw [eY, directionalDerivative_const_smul
    ((hdYf p).mdifferentiableAt (by simp)) (1 / 2) X] at hI1
  -- expand ⟨∇_Y ∇_X Z, Z⟩ likewise
  have hI2 : directionalDerivative Y
        (fun q => g.metricInner q (D.cov q (X q) Z) (Z q)) p
      = g.metricInner p
          (D.cov p (Y p) (D.toAffineConnection.covField X Z)) (Z p)
        + g.metricInner p (D.cov p (X p) Z) (D.cov p (Y p) Z) := by
    have h := D.metric_compat (D.smooth_cov hX hZ) hZ p (Y p)
    rw [dirTangent_eq_directionalDerivative] at h
    exact h
  have eX : (fun q => g.metricInner q (D.cov q (X q) Z) (Z q))
      = fun q => (1 / 2) * directionalDerivative X
          (fun r => g.metricInner r (Z r) (Z r)) q := by
    funext q; exact hhalf X q
  rw [eX, directionalDerivative_const_smul
    ((hdXf p).mdifferentiableAt (by simp)) (1 / 2) Y] at hI2
  -- the bracket term via the commutator identity
  have hbr := hhalf (lieDerivativeVectorField I X Y) p
  rw [lieDerivative_vectorField_eq_bracket hX hY hf p] at hbr
  -- assemble
  rw [curvatureTensorFour_apply, curvatureTensor_apply, g.metricInner_sub_left,
    g.metricInner_sub_left, hbr]
  have hsym : g.metricInner p (D.cov p (Y p) Z) (D.cov p (X p) Z)
      = g.metricInner p (D.cov p (X p) Z) (D.cov p (Y p) Z) :=
    g.metricInner_comm ..
  linarith [hI1, hI2, hsym]

omit [I.Boundaryless] [CompleteSpace E] in
/-- **Math.** Prop. 3.1.1(1), first half: `R(X,Y,Z,W) = −R(Y,X,Z,W)`. -/
theorem curvatureTensorFour_antisymm_left {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (X Y Z W : Π x : M, TangentSpace I x)
    (p : M) :
    curvatureTensorFour D X Y Z W p = -curvatureTensorFour D Y X Z W p := by
  rw [curvatureTensorFour_apply, curvatureTensorFour_apply,
    curvatureTensor_antisymm_first, g.metricInner_neg_left]

/-- **Math.** Prop. 3.1.1(1), second half: `R(X,Y,Z,W) = −R(X,Y,W,Z)` —
polarize `R(X,Y,Z+W,Z+W) = 0`. -/
theorem curvatureTensorFour_antisymm_right {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {X Y Z W : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (hW : IsSmoothVectorField W) (p : M) :
    curvatureTensorFour D X Y Z W p = -curvatureTensorFour D X Y W Z p := by
  have hZW : IsSmoothVectorField (fun q => Z q + W q) := by
    simpa using ((⟨Z, hZ⟩ : SmoothVectorField I M) + ⟨W, hW⟩).smooth
  have h0 := curvatureTensorFour_self_eq_zero D hX hY hZW p
  have hZ0 := curvatureTensorFour_self_eq_zero D hX hY hZ p
  have hW0 := curvatureTensorFour_self_eq_zero D hX hY hW p
  simp only [curvatureTensorFour_apply] at h0 hZ0 hW0 ⊢
  rw [curvatureTensor_add_field D.toAffineConnection hX hY hZ hW] at h0
  simp only [g.metricInner_add_left, g.metricInner_add_right] at h0
  linarith [h0, hZ0, hW0]

/-! ## The first Bianchi identity -/

/-- **Math.** Prop. 3.1.1(3) — **Bianchi's first identity**:
`R(X,Y)Z + R(Z,X)Y + R(Y,Z)X = 0`. Torsion-freeness regroups the six double
covariant derivatives into `∇_X[Y,Z] − ∇_{[Y,Z]}X = [X,[Y,Z]]` and cyclic
companions, and the Jacobi identity finishes. -/
theorem curvatureTensor_firstBianchi {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (p : M) :
    curvatureTensor D.toAffineConnection X Y Z p
      + curvatureTensor D.toAffineConnection Z X Y p
      + curvatureTensor D.toAffineConnection Y Z X p = 0 := by
  -- regroup double derivatives into ∇ of brackets, by torsion-freeness
  have G : ∀ {B C : Π x : M, TangentSpace I x}, IsSmoothVectorField B →
      IsSmoothVectorField C → ∀ A : Π x : M, TangentSpace I x,
      D.cov p (A p) (D.toAffineConnection.covField B C)
        - D.cov p (A p) (D.toAffineConnection.covField C B)
        = D.cov p (A p) (lieDerivativeVectorField I B C) := by
    intro B C hB hC A
    have hBC : IsSmoothVectorField (D.toAffineConnection.covField B C) :=
      D.smooth_cov hB hC
    have hCB : IsSmoothVectorField (D.toAffineConnection.covField C B) :=
      D.smooth_cov hC hB
    rw [← D.toAffineConnection.sub_field p (A p) hBC hCB]
    congr 1
    funext q
    exact D.torsion_free hB hC q
  have GX := G hY hZ X
  have GZ := G hX hY Z
  have GY := G hZ hX Y
  -- pair each ∇ of a bracket with its ∇_{[·,·]} partner, by torsion-freeness
  have PX := D.torsion_free hX (hY.lieDerivativeVectorField hZ) p
  have PZ := D.torsion_free hZ (hX.lieDerivativeVectorField hY) p
  have PY := D.torsion_free hY (hZ.lieDerivativeVectorField hX) p
  -- the nested brackets cancel by the Jacobi identity
  have jac := lieDerivativeVectorField_jacobi_cyclic hX hY hZ p
  have sX : lieDerivativeVectorField I (lieDerivativeVectorField I Y Z) X p
      = -(lieDerivativeVectorField I X (lieDerivativeVectorField I Y Z) p) :=
    VectorField.mlieBracket_swap_apply
  have sZ : lieDerivativeVectorField I (lieDerivativeVectorField I X Y) Z p
      = -(lieDerivativeVectorField I Z (lieDerivativeVectorField I X Y) p) :=
    VectorField.mlieBracket_swap_apply
  have sY : lieDerivativeVectorField I (lieDerivativeVectorField I Z X) Y p
      = -(lieDerivativeVectorField I Y (lieDerivativeVectorField I Z X) p) :=
    VectorField.mlieBracket_swap_apply
  rw [curvatureTensor_apply, curvatureTensor_apply, curvatureTensor_apply]
  rw [sX, sZ, sY] at jac
  linear_combination (norm := module) GX + GZ + GY + PX + PZ + PY - jac

/-- Prop. 3.1.1(3) at the `(0,4)` level:
`R(X,Y,Z,W) + R(Z,X,Y,W) + R(Y,Z,X,W) = 0`. -/
theorem curvatureTensorFour_firstBianchi {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (W : Π x : M, TangentSpace I x) (p : M) :
    curvatureTensorFour D X Y Z W p + curvatureTensorFour D Z X Y W p
      + curvatureTensorFour D Y Z X W p = 0 := by
  have hb := curvatureTensor_firstBianchi D hX hY hZ p
  simp only [curvatureTensorFour_apply]
  rw [← g.metricInner_add_left, ← g.metricInner_add_left, hb,
    g.metricInner_zero_left]

/-! ## The pair-swap symmetry -/

/-- **Math.** Prop. 3.1.1(2): `R(X,Y,Z,W) = R(Z,W,X,Y)` — the classical
combinatorial consequence of the two skew-symmetries and the first Bianchi
identity. -/
theorem curvatureTensorFour_pairSwap {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {X Y Z W : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (hW : IsSmoothVectorField W) (p : M) :
    curvatureTensorFour D X Y Z W p = curvatureTensorFour D Z W X Y p := by
  have Eq1 := curvatureTensorFour_firstBianchi D hY hZ hX W p
  have Eq2 := curvatureTensorFour_firstBianchi D hZ hX hW Y p
  have Eq3 := curvatureTensorFour_firstBianchi D hX hW hY Z p
  have Eq4 := curvatureTensorFour_firstBianchi D hW hY hZ X p
  have ar1 := curvatureTensorFour_antisymm_right D hY hZ hX hW p
  have ar2 := curvatureTensorFour_antisymm_right D hZ hX hY hW p
  have ar3 := curvatureTensorFour_antisymm_right D hX hW hZ hY p
  have ar4 := curvatureTensorFour_antisymm_right D hW hY hZ hX p
  have ar5 := curvatureTensorFour_antisymm_right D hX hY hZ hW p
  have ar6 := curvatureTensorFour_antisymm_right D hW hZ hX hY p
  have al5 := curvatureTensorFour_antisymm_left D Y X W Z p
  have al6 := curvatureTensorFour_antisymm_left D Z W Y X p
  have al7 := curvatureTensorFour_antisymm_left D W Z X Y p
  linarith [Eq1, Eq2, Eq3, Eq4, ar1, ar2, ar3, ar4, ar5, ar6, al5, al6, al7]

/-! ## The second Bianchi identity -/

/-- The **covariant derivative of the curvature tensor** as a `(1,3)`-tensor:
`(∇_X R)(Y,Z)W = ∇_X(R(Y,Z)W) − R(∇_X Y, Z)W − R(Y, ∇_X Z)W − R(Y,Z)(∇_X W)`
(the Leibniz rule defining `∇R`, Petersen §2.2.2 applied to `R`). -/
def covariantDerivativeCurvature (D : AffineConnection I M)
    (X Y Z W : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  fun p => D.cov p (X p) (curvatureTensor D Y Z W)
    - curvatureTensor D (D.covField X Y) Z W p
    - curvatureTensor D Y (D.covField X Z) W p
    - curvatureTensor D Y Z (D.covField X W) p

omit [I.Boundaryless] [CompleteSpace E] in
theorem covariantDerivativeCurvature_apply (D : AffineConnection I M)
    (X Y Z W : Π x : M, TangentSpace I x) (p : M) :
    covariantDerivativeCurvature D X Y Z W p
      = D.cov p (X p) (curvatureTensor D Y Z W)
        - curvatureTensor D (D.covField X Y) Z W p
        - curvatureTensor D Y (D.covField X Z) W p
        - curvatureTensor D Y Z (D.covField X W) p := rfl

omit [I.Boundaryless] [CompleteSpace E] in
/-- `∇_v (A − B − C) = ∇_v A − ∇_v B − ∇_v C` for smooth `A, B, C`. -/
theorem AffineConnection.cov_sub_sub_field (D : AffineConnection I M)
    (p : M) (v : TangentSpace I p) {A B C : Π x : M, TangentSpace I x}
    (hA : IsSmoothVectorField A) (hB : IsSmoothVectorField B)
    (hC : IsSmoothVectorField C) :
    D.cov p v (fun q => A q - B q - C q)
      = D.cov p v A - D.cov p v B - D.cov p v C := by
  have hAB : IsSmoothVectorField (fun q => A q - B q) := by
    simpa using ((⟨A, hA⟩ : SmoothVectorField I M) - ⟨B, hB⟩).smooth
  have e : (fun q => A q - B q - C q)
      = fun q => (fun r => A r - B r) q - C q := rfl
  rw [e, D.sub_field p v hAB hC, D.sub_field p v hA hB]

/-- Expansion of `∇_X (R(Y,Z)W)` into covariant-derivative atoms. -/
theorem cov_curvatureTensor_expand (D : AffineConnection I M)
    {Y Z W : Π x : M, TangentSpace I x}
    (hY : IsSmoothVectorField Y) (hZ : IsSmoothVectorField Z)
    (hW : IsSmoothVectorField W) (p : M) (X_p : TangentSpace I p) :
    D.cov p X_p (curvatureTensor D Y Z W)
      = D.cov p X_p (D.covField Y (D.covField Z W))
        - D.cov p X_p (D.covField Z (D.covField Y W))
        - D.cov p X_p (D.covField (lieDerivativeVectorField I Y Z) W) := by
  have hA : IsSmoothVectorField (D.covField Y (D.covField Z W)) :=
    D.smooth_cov hY (D.smooth_cov hZ hW)
  have hB : IsSmoothVectorField (D.covField Z (D.covField Y W)) :=
    D.smooth_cov hZ (D.smooth_cov hY hW)
  have hC : IsSmoothVectorField
      (D.covField (PetersenLib.lieDerivativeVectorField I Y Z) W) :=
    D.smooth_cov (hY.lieDerivativeVectorField hZ) hW
  exact D.cov_sub_sub_field p X_p hA hB hC

/-- **Math.** Prop. 3.1.1(4) — **Bianchi's second identity**:
`(∇_X R)(Y,Z)W + (∇_Y R)(Z,X)W + (∇_Z R)(X,Y)W = 0` for the Riemannian
connection. Proved by direct expansion: the twelve triple covariant derivatives
cancel in pairs across the cyclic sum, torsion-freeness converts the remaining
`∇_{∇··}`-corrections into bracket terms cancelling the `∇_{[·,·]}`
contributions, and the leftover nested-bracket direction vanishes by the
Jacobi identity. -/
theorem curvatureTensor_secondBianchi {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {X Y Z W : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (hW : IsSmoothVectorField W) (p : M) :
    covariantDerivativeCurvature D.toAffineConnection X Y Z W p
      + covariantDerivativeCurvature D.toAffineConnection Y Z X W p
      + covariantDerivativeCurvature D.toAffineConnection Z X Y W p = 0 := by
  set D' := D.toAffineConnection with hD'
  -- smoothness of all first covariant derivatives
  have cXY : IsSmoothVectorField (D'.covField X Y) := D'.smooth_cov hX hY
  have cYX : IsSmoothVectorField (D'.covField Y X) := D'.smooth_cov hY hX
  have cYZ : IsSmoothVectorField (D'.covField Y Z) := D'.smooth_cov hY hZ
  have cZY : IsSmoothVectorField (D'.covField Z Y) := D'.smooth_cov hZ hY
  have cZX : IsSmoothVectorField (D'.covField Z X) := D'.smooth_cov hZ hX
  have cXZ : IsSmoothVectorField (D'.covField X Z) := D'.smooth_cov hX hZ
  -- (i) direction-slot torsion: ∇_{∇_XY}(∇_Z W) − ∇_{∇_YX}(∇_Z W) = ∇_{[X,Y]}(∇_Z W)
  have Ctor : ∀ {A B : Π x : M, TangentSpace I x}, IsSmoothVectorField A →
      IsSmoothVectorField B → ∀ (S : Π x : M, TangentSpace I x),
      D'.cov p (D'.covField A B p) S - D'.cov p (D'.covField B A p) S
        = D'.cov p (lieDerivativeVectorField I A B p) S := by
    intro A B hA hB S
    rw [← D'.cov_sub_direction]
    congr 1
    simpa using D.torsion_free hA hB p
  have Cxy := Ctor hX hY (D'.covField Z W)
  have Cyz := Ctor hY hZ (D'.covField X W)
  have Czx := Ctor hZ hX (D'.covField Y W)
  -- (ii) field-slot torsion: ∇_A(∇_{∇_XY}W) − ∇_A(∇_{∇_YX}W) = ∇_A(∇_{[X,Y]}W)
  have Ftor : ∀ {A B : Π x : M, TangentSpace I x}, IsSmoothVectorField A →
      IsSmoothVectorField B → ∀ (S : Π x : M, TangentSpace I x),
      D'.cov p (S p) (D'.covField (D'.covField A B) W)
        - D'.cov p (S p) (D'.covField (D'.covField B A) W)
        = D'.cov p (S p) (D'.covField (lieDerivativeVectorField I A B) W) := by
    intro A B hA hB S
    have h₁ : IsSmoothVectorField (D'.covField (D'.covField A B) W) :=
      D'.smooth_cov (D'.smooth_cov hA hB) hW
    have h₂ : IsSmoothVectorField (D'.covField (D'.covField B A) W) :=
      D'.smooth_cov (D'.smooth_cov hB hA) hW
    rw [← D'.sub_field p (S p) h₁ h₂]
    congr 1
    funext q
    simp only [AffineConnection.covField_apply]
    rw [← D'.cov_sub_direction]
    congr 1
    exact D.torsion_free hA hB q
  have Fxy := Ftor hX hY Z
  have Fyz := Ftor hY hZ X
  have Fzx := Ftor hZ hX Y
  -- (iii) the six bracket-of-∇ terms sum to ∇ in a Jacobi-vanishing direction
  have Btor : ∀ {A B C : Π x : M, TangentSpace I x}, IsSmoothVectorField A →
      IsSmoothVectorField B → IsSmoothVectorField C →
      lieDerivativeVectorField I (D'.covField A B) C p
        + lieDerivativeVectorField I C (D'.covField B A) p
        = lieDerivativeVectorField I (lieDerivativeVectorField I A B) C p := by
    intro A B C hA hB hC
    have hswap : lieDerivativeVectorField I C (D'.covField B A) p
        = -(lieDerivativeVectorField I (D'.covField B A) C p) :=
      VectorField.mlieBracket_swap_apply
    have hsub : lieDerivativeVectorField I
          (fun q => D'.covField A B q - D'.covField B A q) C p
        = lieDerivativeVectorField I (D'.covField A B) C p
          - lieDerivativeVectorField I (D'.covField B A) C p :=
      lieDerivativeVectorField_sub_left
        (D'.smooth_cov hA hB) (D'.smooth_cov hB hA) C p
    have e : (fun q => D'.covField A B q - D'.covField B A q)
        = lieDerivativeVectorField I A B := by
      funext q
      exact D.torsion_free hA hB q
    rw [e] at hsub
    rw [hswap]
    linear_combination (norm := module) -hsub
  have Bxy := Btor hX hY hZ
  have Byz := Btor hY hZ hX
  have Bzx := Btor hZ hX hY
  have jac := lieDerivativeVectorField_jacobi_cyclic hX hY hZ p
  have J : D'.cov p (lieDerivativeVectorField I (D'.covField X Y) Z p) W
        + D'.cov p (lieDerivativeVectorField I Z (D'.covField Y X) p) W
        + D'.cov p (lieDerivativeVectorField I (D'.covField Y Z) X p) W
        + D'.cov p (lieDerivativeVectorField I X (D'.covField Z Y) p) W
        + D'.cov p (lieDerivativeVectorField I (D'.covField Z X) Y p) W
        + D'.cov p (lieDerivativeVectorField I Y (D'.covField X Z) p) W
      = 0 := by
    have h₁ : D'.cov p (lieDerivativeVectorField I (D'.covField X Y) Z p) W
          + D'.cov p (lieDerivativeVectorField I Z (D'.covField Y X) p) W
        = D'.cov p (lieDerivativeVectorField I
            (lieDerivativeVectorField I X Y) Z p) W := by
      rw [← D'.add_direction, Bxy]
    have h₂ : D'.cov p (lieDerivativeVectorField I (D'.covField Y Z) X p) W
          + D'.cov p (lieDerivativeVectorField I X (D'.covField Z Y) p) W
        = D'.cov p (lieDerivativeVectorField I
            (lieDerivativeVectorField I Y Z) X p) W := by
      rw [← D'.add_direction, Byz]
    have h₃ : D'.cov p (lieDerivativeVectorField I (D'.covField Z X) Y p) W
          + D'.cov p (lieDerivativeVectorField I Y (D'.covField X Z) p) W
        = D'.cov p (lieDerivativeVectorField I
            (lieDerivativeVectorField I Z X) Y p) W := by
      rw [← D'.add_direction, Bzx]
    have hsum : D'.cov p (lieDerivativeVectorField I
            (lieDerivativeVectorField I X Y) Z p) W
          + D'.cov p (lieDerivativeVectorField I
            (lieDerivativeVectorField I Y Z) X p) W
          + D'.cov p (lieDerivativeVectorField I
            (lieDerivativeVectorField I Z X) Y p) W
        = 0 := by
      rw [← D'.add_direction, ← D'.add_direction, jac, D'.cov_zero_direction]
    linear_combination (norm := module) h₁ + h₂ + h₃ + hsum
  -- expand the three ∇_·(R(·,·)W) heads
  have EX := cov_curvatureTensor_expand D' hY hZ hW p (X p)
  have EY := cov_curvatureTensor_expand D' hZ hX hW p (Y p)
  have EZ := cov_curvatureTensor_expand D' hX hY hW p (Z p)
  -- unfold everything and combine
  simp only [covariantDerivativeCurvature_apply]
  rw [EX, EY, EZ]
  simp only [curvatureTensor_apply]
  linear_combination (norm := module) -Cxy - Cyz - Czx + Fxy + Fyz + Fzx + J

/-! ## Prop. 3.1.1, packaged -/

/-- **Math.** **Prop. 3.1.1 — the symmetries of the curvature tensor**
(Petersen §3.1.1): the Riemannian curvature tensor satisfies
(1) skew-symmetry in the first two and in the last two entries,
`R(X,Y,Z,W) = −R(Y,X,Z,W) = R(Y,X,W,Z)`;
(2) symmetry between the first and second pairs, `R(X,Y,Z,W) = R(Z,W,X,Y)`;
(3) Bianchi's first identity, `R(X,Y)Z + R(Z,X)Y + R(Y,Z)X = 0`;
(4) Bianchi's second identity,
`(∇_Z R)(X,Y)W + (∇_X R)(Y,Z)W + (∇_Y R)(Z,X)W = 0`. -/
theorem curvatureTensor_symmetries {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {X Y Z W : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (hW : IsSmoothVectorField W) (p : M) :
    (curvatureTensorFour D X Y Z W p = -curvatureTensorFour D Y X Z W p
      ∧ curvatureTensorFour D X Y Z W p = curvatureTensorFour D Y X W Z p)
    ∧ curvatureTensorFour D X Y Z W p = curvatureTensorFour D Z W X Y p
    ∧ curvatureTensor D.toAffineConnection X Y Z p
        + curvatureTensor D.toAffineConnection Z X Y p
        + curvatureTensor D.toAffineConnection Y Z X p = 0
    ∧ covariantDerivativeCurvature D.toAffineConnection Z X Y W p
        + covariantDerivativeCurvature D.toAffineConnection X Y Z W p
        + covariantDerivativeCurvature D.toAffineConnection Y Z X W p = 0 := by
  refine ⟨⟨curvatureTensorFour_antisymm_left D X Y Z W p, ?_⟩,
    curvatureTensorFour_pairSwap D hX hY hZ hW p, ?_, ?_⟩
  · rw [curvatureTensorFour_antisymm_left D X Y Z W p,
      curvatureTensorFour_antisymm_right D hY hX hZ hW p, neg_neg]
  · exact curvatureTensor_firstBianchi D hX hY hZ p
  · exact curvatureTensor_secondBianchi D hZ hX hY hW p
