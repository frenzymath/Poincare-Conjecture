import MorganTianLib.Ch03.RicciFlow.CurvatureSecondDerivative

/-!
# Morgan--Tian Ch. 3 - covariant derivatives commute with the Ricci trace

This module identifies the first and corrected second covariant derivatives of
the Ricci tensor with the corresponding contractions of the Riemann tensor.
The proof differentiates in a smooth local orthonormal frame.  The connection
terms contributed by the two contracted frame slots cancel because the matrix
of connection coefficients is antisymmetric, while the paired tensor
components form a symmetric matrix.

Only the multilinearity needed for this contraction is developed here.  A
four-tensor is converted to a bilinear form in its second and fourth slots;
the diagonal sum of that bilinear form is independent of the orthonormal basis.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Compatibility of the two pointwise curvature APIs -/

omit [NeZero (Module.finrank ℝ E)] in
private theorem curvatureFormAt_eq_affineCurvatureFormAt_local
    (g : RiemannianMetric I M) (nabla : AffineConnection I M) (p : M)
    (v w z u : TangentSpace I p) :
    curvatureFormAt g nabla p v w z u = nabla.curvatureFormAt g p v w z u := by
  rw [curvatureFormAt_def]
  symm
  exact nabla.curvatureFormAt_eq g p
    (extendVector_apply p v) (extendVector_apply p w)
    (extendVector_apply p z) (extendVector_apply p u)

private theorem ricciAt_leviCivita_eq_ricciTensorAt_local
    (g : RiemannianMetric I M)
    (hLC : g.leviCivitaConnection.IsLeviCivita g) (p : M)
    (v w : TangentSpace I p) :
    ricciAt g g.leviCivitaConnection hLC p v w = ricciTensorAt g p v w := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  simp only [ricciAt, ricciTensorAt, Riemannian.ricciBilin_apply]
  rw [Riemannian.ricciForm_eq_sum _ v w e,
    Riemannian.ricciForm_eq_sum _ v w e]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact curvatureFormAt_eq_affineCurvatureFormAt_local
    g g.leviCivitaConnection p v (e i) w (e i)

/-- **Math.** The tuple covariant derivative of the Ricci tensor is the
Morgan--Tian three-tensor `covRicci`.
-/
theorem covTensorDerivAlong_ricciTensorField_eq_covRicci
    (g : RiemannianMetric I M)
    (hLC : g.leviCivitaConnection.IsLeviCivita g)
    (U X Y : SmoothVectorField I M) (p : M) :
    covTensorDerivAlong g.leviCivitaConnection U (ricciTensorField g)
        ![X, Y] p =
      covRicci g g.leviCivitaConnection
        hLC U X Y p := by
  have hric (A B : SmoothVectorField I M) :
      ricciTensorField g (fun i => if i = 0 then A else B) =
        ricciField g g.leviCivitaConnection hLC A B := by
    funext q
    change ricciTensorAt g q (A q) (B q) =
      ricciAt g g.leviCivitaConnection hLC q (A q) (B q)
    exact (ricciAt_leviCivita_eq_ricciTensorAt_local g hLC q (A q) (B q)).symm
  have hvec : (![X, Y] : Fin 2 → SmoothVectorField I M) =
      fun i => if i = 0 then X else Y := by
    funext i
    fin_cases i <;> simp
  have h0 : Function.update (fun i : Fin 2 => if i = 0 then X else Y) 0
      (g.leviCivitaConnection.cov U X) =
        fun i => if i = 0 then g.leviCivitaConnection.cov U X else Y := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp
    · rw [Function.update_of_ne hi]
      simp [hi]
  have h1 : Function.update (fun i : Fin 2 => if i = 0 then X else Y) 1
      (g.leviCivitaConnection.cov U Y) =
        fun i => if i = 0 then X else g.leviCivitaConnection.cov U Y := by
    funext i
    by_cases hi : i = 0
    · subst hi
      rw [Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
      simp
    · have hi1 : i = 1 := by omega
      subst hi1
      simp
  rw [hvec, covTensorDerivAlong_apply, covRicci, Fin.sum_univ_two]
  simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, reduceIte, h0, h1, hric]
  ring

/-! ### The required four-tensor multilinearity -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
private theorem isCovariantTensor4_covariantDifferential4_local
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ))
    (hT : IsCovariantTensor4 T)
    (hsm : ∀ X Y Z W, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y Z W))
    (U : SmoothVectorField I M) :
    IsCovariantTensor4
      (fun X Y Z W => covariantDifferential4 nabla T X Y Z W U) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X₁ X₂ Y Z W p
    have hfun : T (X₁ + X₂) Y Z W =
        fun q => T X₁ Y Z W q + T X₂ Y Z W q :=
      funext fun q => hT.add₁ X₁ X₂ Y Z W q
    simp only [covariantDifferential4]
    rw [hfun, U.dir_add p ((hsm X₁ Y Z W).mdifferentiableAt (by simp))
      ((hsm X₂ Y Z W).mdifferentiableAt (by simp)), nabla.add_right U X₁ X₂]
    simp only [hT.add₁]
    ring
  · intro X Y₁ Y₂ Z W p
    have hfun : T X (Y₁ + Y₂) Z W =
        fun q => T X Y₁ Z W q + T X Y₂ Z W q :=
      funext fun q => hT.add₂ X Y₁ Y₂ Z W q
    simp only [covariantDifferential4]
    rw [hfun, U.dir_add p ((hsm X Y₁ Z W).mdifferentiableAt (by simp))
      ((hsm X Y₂ Z W).mdifferentiableAt (by simp)), nabla.add_right U Y₁ Y₂]
    simp only [hT.add₂]
    ring
  · intro X Y Z₁ Z₂ W p
    have hfun : T X Y (Z₁ + Z₂) W =
        fun q => T X Y Z₁ W q + T X Y Z₂ W q :=
      funext fun q => hT.add₃ X Y Z₁ Z₂ W q
    simp only [covariantDifferential4]
    rw [hfun, U.dir_add p ((hsm X Y Z₁ W).mdifferentiableAt (by simp))
      ((hsm X Y Z₂ W).mdifferentiableAt (by simp)), nabla.add_right U Z₁ Z₂]
    simp only [hT.add₃]
    ring
  · intro X Y Z W₁ W₂ p
    have hfun : T X Y Z (W₁ + W₂) =
        fun q => T X Y Z W₁ q + T X Y Z W₂ q :=
      funext fun q => hT.add₄ X Y Z W₁ W₂ q
    simp only [covariantDifferential4]
    rw [hfun, U.dir_add p ((hsm X Y Z W₁).mdifferentiableAt (by simp))
      ((hsm X Y Z W₂).mdifferentiableAt (by simp)), nabla.add_right U W₁ W₂]
    simp only [hT.add₄]
    ring
  · intro f hf X Y Z W p
    have hfun : T (SmoothVectorField.smul f hf X) Y Z W =
        fun q => f q * T X Y Z W q :=
      funext fun q => hT.smul₁ f hf X Y Z W q
    simp only [covariantDifferential4]
    rw [hfun, U.dir_mul p (hf.mdifferentiableAt (by simp))
      ((hsm X Y Z W).mdifferentiableAt (by simp)), nabla.cov_smul_right hf U X]
    simp only [hT.add₁, hT.smul₁]
    ring
  · intro f hf X Y Z W p
    have hfun : T X (SmoothVectorField.smul f hf Y) Z W =
        fun q => f q * T X Y Z W q :=
      funext fun q => hT.smul₂ f hf X Y Z W q
    simp only [covariantDifferential4]
    rw [hfun, U.dir_mul p (hf.mdifferentiableAt (by simp))
      ((hsm X Y Z W).mdifferentiableAt (by simp)), nabla.cov_smul_right hf U Y]
    simp only [hT.add₂, hT.smul₂]
    ring
  · intro f hf X Y Z W p
    have hfun : T X Y (SmoothVectorField.smul f hf Z) W =
        fun q => f q * T X Y Z W q :=
      funext fun q => hT.smul₃ f hf X Y Z W q
    simp only [covariantDifferential4]
    rw [hfun, U.dir_mul p (hf.mdifferentiableAt (by simp))
      ((hsm X Y Z W).mdifferentiableAt (by simp)), nabla.cov_smul_right hf U Z]
    simp only [hT.add₃, hT.smul₃]
    ring
  · intro f hf X Y Z W p
    have hfun : T X Y Z (SmoothVectorField.smul f hf W) =
        fun q => f q * T X Y Z W q :=
      funext fun q => hT.smul₄ f hf X Y Z W q
    simp only [covariantDifferential4]
    rw [hfun, U.dir_mul p (hf.mdifferentiableAt (by simp))
      ((hsm X Y Z W).mdifferentiableAt (by simp)), nabla.cov_smul_right hf U W]
    simp only [hT.add₄, hT.smul₄]
    ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
private theorem isCovariantTensor4_sub_local
    {T S : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ)}
    (hT : IsCovariantTensor4 T) (hS : IsCovariantTensor4 S) :
    IsCovariantTensor4 (fun X Y Z W q => T X Y Z W q - S X Y Z W q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X₁ X₂ Y Z W q; rw [hT.add₁, hS.add₁]; ring
  · intro X Y₁ Y₂ Z W q; rw [hT.add₂, hS.add₂]; ring
  · intro X Y Z₁ Z₂ W q; rw [hT.add₃, hS.add₃]; ring
  · intro X Y Z W₁ W₂ q; rw [hT.add₄, hS.add₄]; ring
  · intro f hf X Y Z W q; rw [hT.smul₁, hS.smul₁]; ring
  · intro f hf X Y Z W q; rw [hT.smul₂, hS.smul₂]; ring
  · intro f hf X Y Z W q; rw [hT.smul₃, hS.smul₃]; ring
  · intro f hf X Y Z W q; rw [hT.smul₄, hS.smul₄]; ring

/-- **Math.** For fixed derivative direction `U`, `nabla_U Rm` is a covariant
four-tensor in its curvature slots.
-/
theorem isCovariantTensor4_covTensorDerivAlong_riemannTensorField
    (g : RiemannianMetric I M) (U : SmoothVectorField I M) :
    IsCovariantTensor4 (fun X Y Z W q =>
      covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
        ![X, Y, Z, W] q) := by
  let nabla := g.leviCivitaConnection
  let T := nabla.curvatureForm g
  let A := fun X Y Z W q =>
    covTensorDerivAlong nabla U (riemannTensorField g) ![X, Y, Z, W] q
  have hA : A = fun X Y Z W => covariantDifferential4 nabla T X Y Z W U := by
    funext X Y Z W q
    exact covTensorDerivAlong_eq_covariantDifferential4 nabla T
      (riemannTensorField g)
      (fun V r => nabla.curvatureFormAt_eq g r rfl rfl rfl rfl)
      U ![X, Y, Z, W] q
  change IsCovariantTensor4 A
  rw [hA]
  exact isCovariantTensor4_covariantDifferential4_local nabla T
    (nabla.curvatureForm_isCovariantTensor4 g)
    (fun X Y Z W => curvatureForm_contMDiff g nabla X Y Z W) U

/-- **Math.** For fixed derivative directions `U,V`, the corrected derivative
`nabla^2_{U,V} Rm` is a covariant four-tensor in its curvature slots.
-/
theorem isCovariantTensor4_secondCovDerivAlong_riemannTensorField
    (g : RiemannianMetric I M) (U V : SmoothVectorField I M) :
    IsCovariantTensor4 (fun X Y Z W q =>
      secondCovDerivAlong g.leviCivitaConnection U V (riemannTensorField g)
        ![X, Y, Z, W] q) := by
  let nabla := g.leviCivitaConnection
  let T := nabla.curvatureForm g
  let dV := fun X Y Z W => covariantDifferential4 nabla T X Y Z W V
  let ddUV := fun X Y Z W => covariantDifferential4 nabla dV X Y Z W U
  let corr := fun X Y Z W =>
    covariantDifferential4 nabla T X Y Z W (nabla.cov U V)
  have hT : IsCovariantTensor4 T := nabla.curvatureForm_isCovariantTensor4 g
  have hsm : ∀ X Y Z W, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y Z W) :=
    fun X Y Z W => curvatureForm_contMDiff g nabla X Y Z W
  have hdV : IsCovariantTensor4 dV :=
    isCovariantTensor4_covariantDifferential4_local nabla T hT hsm V
  have hdVsm : ∀ X Y Z W, ContMDiff I 𝓘(ℝ, ℝ) ∞ (dV X Y Z W) :=
    fun X Y Z W => covariantDifferential4_contMDiff' nabla T hsm X Y Z W V
  have hddUV : IsCovariantTensor4 ddUV :=
    isCovariantTensor4_covariantDifferential4_local nabla dV hdV hdVsm U
  have hcorr : IsCovariantTensor4 corr :=
    isCovariantTensor4_covariantDifferential4_local nabla T hT hsm (nabla.cov U V)
  have hsub : IsCovariantTensor4
      (fun X Y Z W q => ddUV X Y Z W q - corr X Y Z W q) :=
    isCovariantTensor4_sub_local hddUV hcorr
  let A := fun X Y Z W q =>
    secondCovDerivAlong nabla U V (riemannTensorField g) ![X, Y, Z, W] q
  have hA : A = fun X Y Z W q => ddUV X Y Z W q - corr X Y Z W q := by
    funext X Y Z W q
    exact secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
      g U V ![X, Y, Z, W] q
  change IsCovariantTensor4 A
  rw [hA]
  exact hsub

/-! ### A basis-independent contraction of slots two and four -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
private noncomputable def slotsOneThreeBilin
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ)) (hT : IsCovariantTensor4 T)
    (p : M) (X Y : SmoothVectorField I M) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun a b => T X (extendVector p a) Y (extendVector p b) p)
    (fun a₁ a₂ b => by
      have h : T X (extendVector p (a₁ + a₂)) Y (extendVector p b) p =
          T X (extendVector p a₁ + extendVector p a₂) Y (extendVector p b) p :=
        covariantTensor4_congr_apply T hT rfl (by simp) rfl rfl
      rw [h, hT.add₂])
    (fun c a b => by
      have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
      have h : T X (extendVector p (c • a)) Y (extendVector p b) p =
          T X (SmoothVectorField.smul (fun _ => c) hc (extendVector p a)) Y
            (extendVector p b) p :=
        covariantTensor4_congr_apply T hT rfl (by simp) rfl rfl
      rw [h]
      simpa only [smul_eq_mul] using
        hT.smul₂ (fun _ => c) hc X (extendVector p a) Y (extendVector p b) p)
    (fun a b₁ b₂ => by
      have h : T X (extendVector p a) Y (extendVector p (b₁ + b₂)) p =
          T X (extendVector p a) Y (extendVector p b₁ + extendVector p b₂) p :=
        covariantTensor4_congr_apply T hT rfl rfl rfl (by simp)
      rw [h, hT.add₄])
    (fun c a b => by
      have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
      have h : T X (extendVector p a) Y (extendVector p (c • b)) p =
          T X (extendVector p a) Y
            (SmoothVectorField.smul (fun _ => c) hc (extendVector p b)) p :=
        covariantTensor4_congr_apply T hT rfl rfl rfl (by simp)
      rw [h]
      simpa only [smul_eq_mul] using
        hT.smul₄ (fun _ => c) hc X (extendVector p a) Y (extendVector p b) p)

set_option linter.unusedSectionVars false in
private theorem slotsOneThreeBilin_apply_fields
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ)) (hT : IsCovariantTensor4 T)
    (p : M) (X Y P Q : SmoothVectorField I M) :
    slotsOneThreeBilin T hT p X Y (P p) (Q p) = T X P Y Q p := by
  change T X (extendVector p (P p)) Y (extendVector p (Q p)) p = T X P Y Q p
  exact covariantTensor4_congr_apply T hT rfl
    (extendVector_apply p (P p)) rfl (extendVector_apply p (Q p))

private theorem sum_slotsOneThree_eq_std
    (g : RiemannianMetric I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ)) (hT : IsCovariantTensor4 T)
    (p : M) (X Y : SmoothVectorField I M) {ι : Type*} [Fintype ι]
    (e : letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace I p))
    (F : ι → SmoothVectorField I M) (he : ∀ i, e i = F i p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (∑ i, T X (F i) Y (F i) p) =
      ∑ j, T X (extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) j)) Y
        (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) j)) p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let B := slotsOneThreeBilin T hT p X Y
  have hframe : (∑ i, T X (F i) Y (F i) p) = ∑ i, B (e i) (e i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [he i]
    exact (slotsOneThreeBilin_apply_fields T hT p X Y (F i) (F i)).symm
  have hstd : (∑ j, B (stdOrthonormalBasis ℝ (TangentSpace I p) j)
        (stdOrthonormalBasis ℝ (TangentSpace I p) j)) =
      ∑ j, T X (extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) j)) Y
        (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) j)) p := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simpa only [extendVector_apply] using
      (slotsOneThreeBilin_apply_fields T hT p X Y
        (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) j))
        (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) j)))
  calc
    (∑ i, T X (F i) Y (F i) p) = ∑ i, B (e i) (e i) := hframe
    _ = ∑ j, B (stdOrthonormalBasis ℝ (TangentSpace I p) j)
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) :=
      OrthonormalBasis.sum_apply_diagonal_invariant
        e (stdOrthonormalBasis ℝ (TangentSpace I p)) B
    _ = _ := hstd

omit [CompleteSpace E] in
private theorem sum_covariantTensor4_frame_corrections_eq_zero
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) (α : M) {q : M}
    (hq : q ∈ orthoFrameSet (I := I) (M := M) α)
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ)) (hT : IsCovariantTensor4 T)
    (U X Y : SmoothVectorField I M) :
    ∑ j, (T X (nabla.cov U (orthoFrameField g α j)) Y
          (orthoFrameField g α j) q +
        T X (orthoFrameField g α j) Y
          (nabla.cov U (orthoFrameField g α j)) q) = 0 := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let F : Fin (Module.finrank ℝ E) → SmoothVectorField I M :=
    fun j => orthoFrameField g α j
  let e := orthoFrameBasis g α hq
  let B := slotsOneThreeBilin T hT q X Y
  have he : ∀ j, e j = F j q := fun j => orthoFrameBasis_apply g α hq j
  let om : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun j k => g.metricInner q ((nabla.cov U (F j)) q) (e k)
  let S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun j k => B (e k) (e j) + B (e j) (e k)
  have hom : ∀ j k, om j k + om k j = 0 := by
    intro j k
    dsimp [om]
    change inner ℝ ((nabla.cov U (F j)) q) (e k) +
      inner ℝ ((nabla.cov U (F k)) q) (e j) = 0
    rw [inner_tangentSpace_eq_metricInner g q,
      inner_tangentSpace_eq_metricInner g q]
    have h := orthoFrame_connection_antisymm g nabla hLC α hq U j k
    rw [he k, he j]
    simpa only [F] using h
  have hS : ∀ j k, S j k = S k j := by
    intro j k
    dsimp [S]
    ring
  have hzero := sum_antisymm_mul_symm_eq_zero om S hom hS
  have hexpand (j : Fin (Module.finrank ℝ E)) :
      (nabla.cov U (F j)) q = ∑ k, om j k • e k := by
    let w := (nabla.cov U (F j)) q
    have hrepr : w = ∑ k, (inner ℝ (e k) w) • e k := by
      have hcoef : ∀ k, (inner ℝ (e k) w) • (e k : TangentSpace I q) =
          (e.repr w).ofLp k • e k := fun k => by
        rw [e.repr_apply_apply w k]
      rw [Finset.sum_congr rfl fun k _ => hcoef k]
      exact (e.sum_repr w).symm
    change w = ∑ k, om j k • e k
    rw [hrepr]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_tangentSpace_eq_metricInner g q (e k) w,
      g.metricInner_comm q (e k) w]
  have hterm (j : Fin (Module.finrank ℝ E)) :
      T X (nabla.cov U (F j)) Y (F j) q +
          T X (F j) Y (nabla.cov U (F j)) q =
        ∑ k, om j k * S j k := by
    rw [← slotsOneThreeBilin_apply_fields T hT q X Y
        (nabla.cov U (F j)) (F j),
      ← slotsOneThreeBilin_apply_fields T hT q X Y
        (F j) (nabla.cov U (F j)), ← he j, hexpand j]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by simp only [S]; ring
  change ∑ j, (T X (nabla.cov U (F j)) Y (F j) q +
    T X (F j) Y (nabla.cov U (F j)) q) = 0
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  exact hzero

/-! ### The first covariant derivative of Ricci is the trace of `nabla Rm` -/

/-- **Math.** Covariant differentiation commutes with the Ricci contraction in
any smooth local orthonormal frame.
-/
theorem covTensorDerivAlong_ricciTensorField_eq_orthoFrame_sum
    (g : RiemannianMetric I M) (α : M) {q : M}
    (hq : q ∈ orthoFrameSet (I := I) (M := M) α)
    (U X Y : SmoothVectorField I M) :
    covTensorDerivAlong g.leviCivitaConnection U (ricciTensorField g)
        ![X, Y] q =
      ∑ j, covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
        ![X, orthoFrameField g α j, Y, orthoFrameField g α j] q := by
  let nabla := g.leviCivitaConnection
  let hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun A B C r => g.koszulDualSection_dual A B C r)
  rw [covTensorDerivAlong_ricciTensorField_eq_covRicci g hLC]
  rw [covRicci_eq_frame_sum g nabla hLC α hq U X Y]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (covTensorDerivAlong_eq_covariantDifferential4 nabla
    (nabla.curvatureForm g) (riemannTensorField g)
    (fun Z r => nabla.curvatureFormAt_eq g r rfl rfl rfl rfl)
    U ![X, orthoFrameField g α j, Y, orthoFrameField g α j] q).symm

/-- **Math.** The first covariant derivative of Ricci is the standard
orthonormal trace of the first covariant derivative of Riemann.
-/
theorem covTensorDerivAlong_ricciTensorField_eq_stdOrthonormalBasis_sum
    (g : RiemannianMetric I M) (U X Y : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    covTensorDerivAlong g.leviCivitaConnection U (ricciTensorField g)
        ![X, Y] p =
      ∑ j, covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
        ![X, extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) j), Y,
          extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) j)] p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let F : Fin (Module.finrank ℝ E) → SmoothVectorField I M :=
    fun j => orthoFrameField g p j
  have hp : p ∈ orthoFrameSet (I := I) (M := M) p := mem_orthoFrameSet_self p
  let e := orthoFrameBasis g p hp
  have he : ∀ j, e j = F j p := fun j => orthoFrameBasis_apply g p hp j
  let T := fun A B C D q =>
    covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
      ![A, B, C, D] q
  have hT : IsCovariantTensor4 T :=
    isCovariantTensor4_covTensorDerivAlong_riemannTensorField g U
  calc
    covTensorDerivAlong g.leviCivitaConnection U (ricciTensorField g) ![X, Y] p =
        ∑ j, T X (F j) Y (F j) p := by
          simpa only [T, F] using
            covTensorDerivAlong_ricciTensorField_eq_orthoFrame_sum g p hp U X Y
    _ = ∑ j, T X (extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) j)) Y
        (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) j)) p :=
      sum_slotsOneThree_eq_std g T hT p X Y e F he
    _ = _ := by rfl

/-! ### The corrected second derivative of Ricci is the trace of `nabla^2 Rm` -/

/-- **Math.** In the smooth orthonormal frame centred at `p`, the corrected
second covariant derivative of Ricci is the corresponding trace of the
corrected second covariant derivative of Riemann.
-/
theorem secondCovDerivAlong_ricciTensorField_eq_orthoFrame_sum
    (g : RiemannianMetric I M) (U V X Y : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    secondCovDerivAlong g.leviCivitaConnection U V (ricciTensorField g)
        ![X, Y] p =
      ∑ j, secondCovDerivAlong g.leviCivitaConnection U V
        (riemannTensorField g)
        ![X, orthoFrameField g p j, Y, orthoFrameField g p j] p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let nabla := g.leviCivitaConnection
  let hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun A B C r => g.koszulDualSection_dual A B C r)
  let F : Fin (Module.finrank ℝ E) → SmoothVectorField I M :=
    fun j => orthoFrameField g p j
  have hp : p ∈ orthoFrameSet (I := I) (M := M) p := mem_orthoFrameSet_self p
  have hcov (D A B : SmoothVectorField I M) :
      covTensorDerivAlong nabla D (ricciTensorField g) ![A, B] p =
        ∑ j, covTensorDerivAlong nabla D (riemannTensorField g)
          ![A, F j, B, F j] p := by
    simpa only [nabla, F] using
      covTensorDerivAlong_ricciTensorField_eq_orthoFrame_sum g p hp D A B
  have hdir :
      U.dir (covTensorDerivAlong nabla V (ricciTensorField g) ![X, Y]) p =
        ∑ j, U.dir (covTensorDerivAlong nabla V (riemannTensorField g)
          ![X, F j, Y, F j]) p := by
    have hrep : covTensorDerivAlong nabla V (ricciTensorField g) ![X, Y] =ᶠ[𝓝 p]
        fun q => ∑ j, covTensorDerivAlong nabla V (riemannTensorField g)
          ![X, F j, Y, F j] q := by
      filter_upwards [(isOpen_orthoFrameSet
        (I := I) (M := M) p).mem_nhds hp] with q hq
      simpa only [nabla, F] using
        covTensorDerivAlong_ricciTensorField_eq_orthoFrame_sum g p hq V X Y
    rw [dir_congr_nhds U hrep]
    apply dir_finset_sum U Finset.univ p
    intro j _
    have heq : covTensorDerivAlong nabla V (riemannTensorField g)
          ![X, F j, Y, F j] =
        covariantDifferential4 nabla (nabla.curvatureForm g)
          X (F j) Y (F j) V := by
      funext q
      exact covTensorDerivAlong_eq_covariantDifferential4 nabla
        (nabla.curvatureForm g) (riemannTensorField g)
        (fun Z r => nabla.curvatureFormAt_eq g r rfl rfl rfl rfl)
        V ![X, F j, Y, F j] q
    rw [heq]
    exact (covariantDifferential4_contMDiff' nabla (nabla.curvatureForm g)
      (fun A B C D => curvatureForm_contMDiff g nabla A B C D)
      X (F j) Y (F j) V).mdifferentiableAt (by norm_num)
  have hcorr : ∑ j, (
      covTensorDerivAlong nabla V (riemannTensorField g)
          ![X, nabla.cov U (F j), Y, F j] p +
      covTensorDerivAlong nabla V (riemannTensorField g)
          ![X, F j, Y, nabla.cov U (F j)] p) = 0 := by
    let T := fun A B C D q =>
      covTensorDerivAlong nabla V (riemannTensorField g) ![A, B, C, D] q
    have hT : IsCovariantTensor4 T := by
      simpa only [T, nabla] using
        isCovariantTensor4_covTensorDerivAlong_riemannTensorField g V
    simpa only [T, F] using
      sum_covariantTensor4_frame_corrections_eq_zero
        g nabla hLC p hp T hT U X Y
  rw [secondCovDerivAlong, covTensorDerivAlong_apply]
  simp only [Fin.sum_univ_two]
  have hu0 : Function.update ![X, Y] 0 (nabla.cov U (![X, Y] 0)) =
      ![nabla.cov U X, Y] := by
    funext i
    fin_cases i <;> simp
  have hu1 : Function.update ![X, Y] 1 (nabla.cov U (![X, Y] 1)) =
      ![X, nabla.cov U Y] := by
    funext i
    fin_cases i <;> simp
  rw [hdir, hu0, hu1, hcov V (nabla.cov U X) Y,
    hcov V X (nabla.cov U Y), hcov (nabla.cov U V) X Y]
  have hsecond (j : Fin (Module.finrank ℝ E)) :
      secondCovDerivAlong nabla U V (riemannTensorField g)
          ![X, F j, Y, F j] p =
        U.dir (covTensorDerivAlong nabla V (riemannTensorField g)
          ![X, F j, Y, F j]) p
          - covTensorDerivAlong nabla V (riemannTensorField g)
              ![nabla.cov U X, F j, Y, F j] p
          - covTensorDerivAlong nabla V (riemannTensorField g)
              ![X, nabla.cov U (F j), Y, F j] p
          - covTensorDerivAlong nabla V (riemannTensorField g)
              ![X, F j, nabla.cov U Y, F j] p
          - covTensorDerivAlong nabla V (riemannTensorField g)
              ![X, F j, Y, nabla.cov U (F j)] p
          - covTensorDerivAlong nabla (nabla.cov U V) (riemannTensorField g)
              ![X, F j, Y, F j] p := by
    rw [secondCovDerivAlong, covTensorDerivAlong_apply]
    simp only [Fin.sum_univ_four]
    have h0 : Function.update ![X, F j, Y, F j] 0
          (nabla.cov U (![X, F j, Y, F j] 0)) =
        ![nabla.cov U X, F j, Y, F j] := by
      funext i
      fin_cases i <;> simp
    have h1 : Function.update ![X, F j, Y, F j] 1
          (nabla.cov U (![X, F j, Y, F j] 1)) =
        ![X, nabla.cov U (F j), Y, F j] := by
      funext i
      fin_cases i <;> simp
    have h2 : Function.update ![X, F j, Y, F j] 2
          (nabla.cov U (![X, F j, Y, F j] 2)) =
        ![X, F j, nabla.cov U Y, F j] := by
      funext i
      fin_cases i <;> simp
    have h3 : Function.update ![X, F j, Y, F j] 3
          (nabla.cov U (![X, F j, Y, F j] 3)) =
        ![X, F j, Y, nabla.cov U (F j)] := by
      funext i
      fin_cases i <;> simp
    rw [h0, h1, h2, h3]
    ring
  change _ = ∑ j, secondCovDerivAlong nabla U V (riemannTensorField g)
    ![X, F j, Y, F j] p
  have hsum :
      (∑ j, secondCovDerivAlong nabla U V (riemannTensorField g)
        ![X, F j, Y, F j] p) =
        ∑ j, (U.dir (covTensorDerivAlong nabla V (riemannTensorField g)
          ![X, F j, Y, F j]) p
          - covTensorDerivAlong nabla V (riemannTensorField g)
              ![nabla.cov U X, F j, Y, F j] p
          - covTensorDerivAlong nabla V (riemannTensorField g)
              ![X, nabla.cov U (F j), Y, F j] p
          - covTensorDerivAlong nabla V (riemannTensorField g)
              ![X, F j, nabla.cov U Y, F j] p
          - covTensorDerivAlong nabla V (riemannTensorField g)
              ![X, F j, Y, nabla.cov U (F j)] p
          - covTensorDerivAlong nabla (nabla.cov U V) (riemannTensorField g)
              ![X, F j, Y, F j] p) := by
    exact Finset.sum_congr rfl fun j _ => hsecond j
  have hsum' := hsum
  simp only [Finset.sum_sub_distrib] at hsum'
  have hcorr' := hcorr
  rw [Finset.sum_add_distrib] at hcorr'
  linear_combination hsum'.symm + hcorr'

/-- **Math.** The corrected second covariant derivative of Ricci is the
standard orthonormal trace of the corrected second derivative of Riemann.
-/
theorem secondCovDerivAlong_ricciTensorField_eq_stdOrthonormalBasis_sum
    (g : RiemannianMetric I M) (U V X Y : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    secondCovDerivAlong g.leviCivitaConnection U V (ricciTensorField g)
        ![X, Y] p =
      ∑ j, secondCovDerivAlong g.leviCivitaConnection U V
        (riemannTensorField g)
        ![X, extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) j), Y,
          extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) j)] p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let F : Fin (Module.finrank ℝ E) → SmoothVectorField I M :=
    fun j => orthoFrameField g p j
  have hp : p ∈ orthoFrameSet (I := I) (M := M) p := mem_orthoFrameSet_self p
  let e := orthoFrameBasis g p hp
  have he : ∀ j, e j = F j p := fun j => orthoFrameBasis_apply g p hp j
  let T := fun A B C D q =>
    secondCovDerivAlong g.leviCivitaConnection U V (riemannTensorField g)
      ![A, B, C, D] q
  have hT : IsCovariantTensor4 T :=
    isCovariantTensor4_secondCovDerivAlong_riemannTensorField g U V
  calc
    secondCovDerivAlong g.leviCivitaConnection U V (ricciTensorField g) ![X, Y] p =
        ∑ j, T X (F j) Y (F j) p := by
          simpa only [T, F] using
            secondCovDerivAlong_ricciTensorField_eq_orthoFrame_sum g U V X Y p
    _ = ∑ j, T X (extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) j)) Y
        (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) j)) p :=
      sum_slotsOneThree_eq_std g T hT p X Y e F he
    _ = _ := by rfl

#print axioms MorganTianLib.covTensorDerivAlong_ricciTensorField_eq_orthoFrame_sum
#print axioms MorganTianLib.covTensorDerivAlong_ricciTensorField_eq_stdOrthonormalBasis_sum
#print axioms MorganTianLib.secondCovDerivAlong_ricciTensorField_eq_orthoFrame_sum
#print axioms MorganTianLib.secondCovDerivAlong_ricciTensorField_eq_stdOrthonormalBasis_sum

end MorganTianLib

end
