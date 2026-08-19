import Topping.Riemannian.VariationScalar
import Topping.Riemannian.CurvatureMultilinear
import Topping.Riemannian.FrameTrace

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Multilinearity of the corrected second derivative -/

/-- **Math.** The corrected second covariant derivative of `Rm` remains
pointwise multilinear in its four curvature slots. -/
theorem isPointwiseMultilinear_secondCovDerivAlong_riemannTensorField
    (g : RiemannianMetric I M) (U V : SmoothVectorField I M) (p : M) :
    IsPointwiseMultilinear
      (secondCovDerivAlong g.leviCivitaConnection U V (riemannTensorField g)) p := by
  have h₁ := isPointwiseMultilinear_covDerivAlong_covDerivAlong_riemannTensorField g V U p
  have h₂ := isPointwiseMultilinear_covDerivAlong_riemannTensorField g
    (g.leviCivitaConnection.cov U V) p
  refine {
    tensorial := fun Y Z hYZ => by
      simp only [secondCovDerivAlong]
      rw [h₁.tensorial Y Z hYZ, h₂.tensorial Y Z hYZ]
    add := fun i v x y => by
      unfold secondCovDerivAlong
      change
        (pointwiseValue
            (covDerivAlong g.leviCivitaConnection U
              (covDerivAlong g.leviCivitaConnection V (riemannTensorField g))) p
            (Function.update v i (x + y)) -
          pointwiseValue
            (covDerivAlong g.leviCivitaConnection
              (g.leviCivitaConnection.cov U V) (riemannTensorField g)) p
            (Function.update v i (x + y))) =
        (pointwiseValue
            (covDerivAlong g.leviCivitaConnection U
              (covDerivAlong g.leviCivitaConnection V (riemannTensorField g))) p
            (Function.update v i x) -
          pointwiseValue
            (covDerivAlong g.leviCivitaConnection
              (g.leviCivitaConnection.cov U V) (riemannTensorField g)) p
            (Function.update v i x)) +
        (pointwiseValue
            (covDerivAlong g.leviCivitaConnection U
              (covDerivAlong g.leviCivitaConnection V (riemannTensorField g))) p
            (Function.update v i y) -
          pointwiseValue
            (covDerivAlong g.leviCivitaConnection
              (g.leviCivitaConnection.cov U V) (riemannTensorField g)) p
            (Function.update v i y))
      rw [h₁.add i v x y, h₂.add i v x y]
      ring
    smul := fun i v c x => by
      unfold secondCovDerivAlong
      change
        (pointwiseValue
            (covDerivAlong g.leviCivitaConnection U
              (covDerivAlong g.leviCivitaConnection V (riemannTensorField g))) p
            (Function.update v i (c • x)) -
          pointwiseValue
            (covDerivAlong g.leviCivitaConnection
              (g.leviCivitaConnection.cov U V) (riemannTensorField g)) p
            (Function.update v i (c • x))) =
        c * (pointwiseValue
            (covDerivAlong g.leviCivitaConnection U
              (covDerivAlong g.leviCivitaConnection V (riemannTensorField g))) p
            (Function.update v i x) -
          pointwiseValue
            (covDerivAlong g.leviCivitaConnection
              (g.leviCivitaConnection.cov U V) (riemannTensorField g)) p
            (Function.update v i x))
      rw [h₁.smul i v c x, h₂.smul i v c x]
      ring }

theorem secondCovDerivAlong_ricciTensorField_eq_orthoFrame_sum
    (g : RiemannianMetric I M) (U V X Y : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    secondCovDerivAlong g.leviCivitaConnection U V (ricciTensorField g)
        ![X, Y] p =
      ∑ j, secondCovDerivAlong g.leviCivitaConnection U V
        (riemannTensorField g)
        ![X, MorganTianLib.orthoFrameField g p j, Y,
          MorganTianLib.orthoFrameField g p j] p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let nabla := g.leviCivitaConnection
  let F : Fin (Module.finrank ℝ E) → SmoothVectorField I M :=
    fun j => MorganTianLib.orthoFrameField g p j
  have hp : p ∈ MorganTianLib.orthoFrameSet (I := I) (M := M) p :=
    MorganTianLib.mem_orthoFrameSet_self p
  have hcov (D A B : SmoothVectorField I M) :
      covDerivAlong nabla D (ricciTensorField g) ![A, B] p =
        ∑ j, covDerivAlong nabla D (riemannTensorField g)
          ![A, F j, B, F j] p := by
    rw [show ![A, B] = (fun i => if i = 0 then A else B) by
      funext i; fin_cases i <;> simp]
    rw [covDerivAlong_ricciTensorField]
    rw [MorganTianLib.covRicci_eq_frame_sum g nabla
      (isLeviCivita_leviCivitaConnection g) p hp D A B]
    apply Finset.sum_congr rfl
    intro j hj
    exact (covDerivAlong_eq_covariantDifferential4 nabla
      (nabla.curvatureForm g) (riemannTensorField g)
      (fun Z q => riemannCurvatureAt_eq g q rfl rfl rfl rfl)
      D ![A, F j, B, F j] p).symm
  have hdir :
      U.dir (covDerivAlong nabla V (ricciTensorField g) ![X, Y]) p =
        ∑ j, U.dir (covDerivAlong nabla V (riemannTensorField g)
          ![X, F j, Y, F j]) p := by
    have hrep : covDerivAlong nabla V (ricciTensorField g) ![X, Y] =ᶠ[𝓝 p]
        fun q => ∑ j, covDerivAlong nabla V (riemannTensorField g)
          ![X, F j, Y, F j] q := by
      filter_upwards [(MorganTianLib.isOpen_orthoFrameSet
        (I := I) (M := M) p).mem_nhds hp] with q hq
      rw [show ![X, Y] = (fun i => if i = 0 then X else Y) by
        funext i; fin_cases i <;> simp]
      rw [covDerivAlong_ricciTensorField]
      rw [MorganTianLib.covRicci_eq_frame_sum g nabla
        (isLeviCivita_leviCivitaConnection g) p hq V X Y]
      apply Finset.sum_congr rfl
      intro j hj
      exact (covDerivAlong_eq_covariantDifferential4 nabla
        (nabla.curvatureForm g) (riemannTensorField g)
        (fun Z r => riemannCurvatureAt_eq g r rfl rfl rfl rfl)
        V ![X, F j, Y, F j] q).symm
    rw [MorganTianLib.dir_congr_nhds U hrep]
    have hsm : ∀ A B C D, ContMDiff I 𝓘(ℝ, ℝ) ∞
        (nabla.curvatureForm g A B C D) :=
      fun A B C D => MorganTianLib.curvatureForm_contMDiff g nabla A B C D
    apply MorganTianLib.dir_finset_sum U Finset.univ p
    intro j hj
    have heq : covDerivAlong nabla V (riemannTensorField g)
          ![X, F j, Y, F j] =
        MorganTianLib.covariantDifferential4 nabla (nabla.curvatureForm g)
          X (F j) Y (F j) V := by
      funext q
      exact covDerivAlong_eq_covariantDifferential4 nabla
        (nabla.curvatureForm g) (riemannTensorField g)
        (fun Z r => riemannCurvatureAt_eq g r rfl rfl rfl rfl)
        V ![X, F j, Y, F j] q
    rw [heq]
    exact (covariantDifferential4_contMDiff nabla (nabla.curvatureForm g)
      hsm X (F j) Y (F j) V).mdifferentiableAt (by norm_num)
  have hcorr : ∑ j, (
      covDerivAlong nabla V (riemannTensorField g)
          ![X, (nabla.cov U (F j)), Y, F j] p +
      covDerivAlong nabla V (riemannTensorField g)
          ![X, F j, Y, (nabla.cov U (F j))] p) = 0 := by
    let A := covDerivAlong nabla V (riemannTensorField g)
    have hA := isPointwiseMultilinear_covDerivAlong_riemannTensorField g V p
    let e := MorganTianLib.orthoFrameBasis g p hp
    have hev : ∀ k, e k = F k p := by
      intro k
      exact MorganTianLib.orthoFrameBasis_apply g p hp k
    let om : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
      fun j k => g.metricInner p (e k) ((nabla.cov U (F j)) p)
    have hom : ∀ j k, om j k + om k j = 0 := by
      intro j k
      dsimp [om]
      change g.metricInner p (e k) ((nabla.cov U (F j)) p) +
        g.metricInner p (e j) ((nabla.cov U (F k)) p) = 0
      rw [g.metricInner_comm p (e k) _, g.metricInner_comm p (e j) _]
      have hh := MorganTianLib.orthoFrame_connection_antisymm g nabla
        (isLeviCivita_leviCivitaConnection g) p hp U j k
      rw [hev k, hev j]
      simpa only [F] using hh
    let S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun j k =>
      pointwiseValue A p ![X p, e k, Y p, F j p] +
        pointwiseValue A p ![X p, F j p, Y p, e k]
    have hS : ∀ j k, S j k = S k j := by
      intro j k
      dsimp [S]
      rw [hev k, hev j]
      ring
    have hzero := MorganTianLib.sum_antisymm_mul_symm_eq_zero om S hom hS
    have hterm : ∀ j k,
        om j k * S j k =
          g.metricInner p (e k) ((nabla.cov U (F j)) p) *
            (covDerivAlong nabla V (riemannTensorField g)
                ![X, F k, Y, F j] p +
             covDerivAlong nabla V (riemannTensorField g)
                ![X, F j, Y, F k] p) := by
      intro j k
      dsimp [om, S]
      have hv₁ := pointwiseValue_eq hA.tensorial
        ![X, F k, Y, F j]
      have hv₂ := pointwiseValue_eq hA.tensorial
        ![X, F j, Y, F k]
      have hv₁' : pointwiseValue A p ![X p, e k, Y p, F j p] =
          A ![X, F k, Y, F j] p := by
        rw [hev k]
        change pointwiseValue (covDerivAlong g.leviCivitaConnection V
          (riemannTensorField g)) p ![X p, F k p, Y p, F j p] =
          covDerivAlong g.leviCivitaConnection V (riemannTensorField g)
            ![X, F k, Y, F j] p
        have hargs : (![X p, F k p, Y p, F j p] :
            Fin 4 → TangentSpace I p) = fun i => (![X, F k, Y, F j] i) p := by
          funext i; fin_cases i <;> rfl
        rw [hargs]
        simpa [A, nabla] using hv₁
      have hv₂' : pointwiseValue A p ![X p, F j p, Y p, e k] =
          A ![X, F j, Y, F k] p := by
        rw [hev k]
        change pointwiseValue (covDerivAlong g.leviCivitaConnection V
          (riemannTensorField g)) p ![X p, F j p, Y p, F k p] =
          covDerivAlong g.leviCivitaConnection V (riemannTensorField g)
            ![X, F j, Y, F k] p
        have hargs : (![X p, F j p, Y p, F k p] :
            Fin 4 → TangentSpace I p) = fun i => (![X, F j, Y, F k] i) p := by
          funext i; fin_cases i <;> rfl
        rw [hargs]
        simpa [A, nabla] using hv₂
      rw [hv₁', hv₂']
    have hexpand : ∀ j,
        covDerivAlong nabla V (riemannTensorField g)
            ![X, (nabla.cov U (F j)), Y, F j] p +
        covDerivAlong nabla V (riemannTensorField g)
            ![X, F j, Y, (nabla.cov U (F j))] p =
          ∑ k, om j k * S j k := by
      intro j
      let w := (nabla.cov U (F j)) p
      let v : Fin 4 → TangentSpace I p := ![X p, F j p, Y p, F j p]
      have hbase1 :
          covDerivAlong nabla V (riemannTensorField g)
              ![X, (nabla.cov U (F j)), Y, F j] p =
            pointwiseValue A p (Function.update v 1 w) := by
        have hh := pointwiseValue_eq hA.tensorial
          ![X, (nabla.cov U (F j)), Y, F j]
        have hargs : (Function.update v 1 w : Fin 4 → TangentSpace I p) =
            fun i => (![X, (nabla.cov U (F j)), Y, F j] i) p := by
          funext i
          fin_cases i <;> simp [v, w]
        rw [hargs]
        exact hh.symm
      have hbase3 :
          covDerivAlong nabla V (riemannTensorField g)
              ![X, F j, Y, (nabla.cov U (F j))] p =
            pointwiseValue A p (Function.update v 3 w) := by
        have hh := pointwiseValue_eq hA.tensorial
          ![X, F j, Y, (nabla.cov U (F j))]
        have hargs : (Function.update v 3 w : Fin 4 → TangentSpace I p) =
            fun i => (![X, F j, Y, (nabla.cov U (F j))] i) p := by
          funext i
          fin_cases i <;> simp [v, w]
        rw [hargs]
        exact hh.symm
      have h1 := pointwiseValue_expand_slot g hA 1 v w e
      have h3 := pointwiseValue_expand_slot g hA 3 v w e
      have hu1 : ∀ k,
          pointwiseValue A p (Function.update v 1 (e k)) =
            A ![X, F k, Y, F j] p := by
        intro k
        have hh := pointwiseValue_eq hA.tensorial ![X, F k, Y, F j]
        have hargs : (Function.update v 1 (e k) : Fin 4 → TangentSpace I p) =
            fun i => (![X, F k, Y, F j] i) p := by
          funext i
          fin_cases i <;> simp [v, hev]
        rw [hargs]
        exact hh
      have hu3 : ∀ k,
          pointwiseValue A p (Function.update v 3 (e k)) =
            A ![X, F j, Y, F k] p := by
        intro k
        have hh := pointwiseValue_eq hA.tensorial ![X, F j, Y, F k]
        have hargs : (Function.update v 3 (e k) : Fin 4 → TangentSpace I p) =
            fun i => (![X, F j, Y, F k] i) p := by
          funext i
          fin_cases i <;> simp [v, hev]
        rw [hargs]
        exact hh
      rw [hbase1, hbase3, h1, h3]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hu1' : pointwiseValue (covDerivAlong g.leviCivitaConnection V
          (riemannTensorField g)) p (Function.update v 1 (e k)) =
          covDerivAlong g.leviCivitaConnection V (riemannTensorField g)
            ![X, F k, Y, F j] p := by
        simpa [A, nabla] using hu1 k
      have hu3' : pointwiseValue (covDerivAlong g.leviCivitaConnection V
          (riemannTensorField g)) p (Function.update v 3 (e k)) =
          covDerivAlong g.leviCivitaConnection V (riemannTensorField g)
            ![X, F j, Y, F k] p := by
        simpa [A, nabla] using hu3 k
      rw [hu1', hu3']
      simpa [w, nabla, mul_add] using (hterm j k).symm
    rw [Finset.sum_congr rfl fun j _ => hexpand j, hzero]
  rw [secondCovDerivAlong, covDerivAlong_apply]
  simp only [Fin.sum_univ_two]
  have hu0 : Function.update ![X, Y] 0 (nabla.cov U (![X, Y] 0)) =
      ![nabla.cov U X, Y] := by
    funext i; fin_cases i <;> simp
  have hu1 : Function.update ![X, Y] 1 (nabla.cov U (![X, Y] 1)) =
      ![X, nabla.cov U Y] := by
    funext i; fin_cases i <;> simp
  rw [hdir, hu0, hu1, hcov V (nabla.cov U X) Y,
    hcov V X (nabla.cov U Y), hcov (nabla.cov U V) X Y]
  have hsecond (j : Fin (Module.finrank ℝ E)) :
      secondCovDerivAlong nabla U V (riemannTensorField g)
          ![X, F j, Y, F j] p =
        U.dir (covDerivAlong nabla V (riemannTensorField g)
          ![X, F j, Y, F j]) p
          - covDerivAlong nabla V (riemannTensorField g)
              ![nabla.cov U X, F j, Y, F j] p
          - covDerivAlong nabla V (riemannTensorField g)
              ![X, nabla.cov U (F j), Y, F j] p
          - covDerivAlong nabla V (riemannTensorField g)
              ![X, F j, nabla.cov U Y, F j] p
          - covDerivAlong nabla V (riemannTensorField g)
              ![X, F j, Y, nabla.cov U (F j)] p
          - covDerivAlong nabla (nabla.cov U V) (riemannTensorField g)
              ![X, F j, Y, F j] p := by
    rw [secondCovDerivAlong, covDerivAlong_apply]
    simp only [Fin.sum_univ_four]
    have h0 : Function.update ![X, F j, Y, F j] 0
          (nabla.cov U (![X, F j, Y, F j] 0)) =
        ![nabla.cov U X, F j, Y, F j] := by
      funext i; fin_cases i <;> simp
    have h1 : Function.update ![X, F j, Y, F j] 1
          (nabla.cov U (![X, F j, Y, F j] 1)) =
        ![X, nabla.cov U (F j), Y, F j] := by
      funext i; fin_cases i <;> simp
    have h2 : Function.update ![X, F j, Y, F j] 2
          (nabla.cov U (![X, F j, Y, F j] 2)) =
        ![X, F j, nabla.cov U Y, F j] := by
      funext i; fin_cases i <;> simp
    have h3 : Function.update ![X, F j, Y, F j] 3
          (nabla.cov U (![X, F j, Y, F j] 3)) =
        ![X, F j, Y, nabla.cov U (F j)] := by
      funext i; fin_cases i <;> simp
    rw [h0, h1, h2, h3]
    ring
  change _ = ∑ j, secondCovDerivAlong nabla U V (riemannTensorField g)
    ![X, F j, Y, F j] p
  have hsum :
      (∑ j, secondCovDerivAlong nabla U V (riemannTensorField g)
        ![X, F j, Y, F j] p) =
        ∑ j, (U.dir (covDerivAlong nabla V (riemannTensorField g)
          ![X, F j, Y, F j]) p
          - covDerivAlong nabla V (riemannTensorField g)
              ![nabla.cov U X, F j, Y, F j] p
          - covDerivAlong nabla V (riemannTensorField g)
              ![X, nabla.cov U (F j), Y, F j] p
          - covDerivAlong nabla V (riemannTensorField g)
              ![X, F j, nabla.cov U Y, F j] p
          - covDerivAlong nabla V (riemannTensorField g)
              ![X, F j, Y, nabla.cov U (F j)] p
          - covDerivAlong nabla (nabla.cov U V) (riemannTensorField g)
              ![X, F j, Y, F j] p) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hsecond j
  have hsum' := hsum
  simp only [Finset.sum_sub_distrib] at hsum'
  have hcorr' := hcorr
  rw [Finset.sum_add_distrib] at hcorr'
  linear_combination hsum'.symm + hcorr'

theorem secondCovDerivAlong_ricciTensorField_eq_stdOrthonormalBasis_sum
    (g : RiemannianMetric I M) (U V X Y : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    secondCovDerivAlong g.leviCivitaConnection U V (ricciTensorField g)
        ![X, Y] p =
      ∑ j, secondCovDerivAlong g.leviCivitaConnection U V
        (riemannTensorField g)
        ![X, MorganTianLib.extendVector p
            (stdOrthonormalBasis ℝ (TangentSpace I p) j), Y,
          MorganTianLib.extendVector p
            (stdOrthonormalBasis ℝ (TangentSpace I p) j)] p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let nabla := g.leviCivitaConnection
  let A := secondCovDerivAlong nabla U V (riemannTensorField g)
  have hA := isPointwiseMultilinear_secondCovDerivAlong_riemannTensorField g U V p
  have hp : p ∈ MorganTianLib.orthoFrameSet (I := I) (M := M) p :=
    MorganTianLib.mem_orthoFrameSet_self p
  let F : Fin (Module.finrank ℝ E) → SmoothVectorField I M :=
    fun j => MorganTianLib.orthoFrameField g p j
  let e := MorganTianLib.orthoFrameBasis g p hp
  have he : ∀ j, e j = F j p := by
    intro j
    exact MorganTianLib.orthoFrameBasis_apply g p hp j
  let B : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun a b => pointwiseValue A p ![X p, a, Y p, b])
      (fun a₁ a₂ b => by
        have h := hA.add 1
          (![X p, 0, Y p, b] : Fin 4 → TangentSpace I p) a₁ a₂
        have harg : Function.update
              (![X p, 0, Y p, b] : Fin 4 → TangentSpace I p) 1 (a₁ + a₂) =
            ![X p, a₁ + a₂, Y p, b] := by
          funext i
          fin_cases i <;> simp
        have harg₁ : Function.update
              (![X p, 0, Y p, b] : Fin 4 → TangentSpace I p) 1 a₁ =
            ![X p, a₁, Y p, b] := by
          funext i
          fin_cases i <;> simp
        have harg₂ : Function.update
              (![X p, 0, Y p, b] : Fin 4 → TangentSpace I p) 1 a₂ =
            ![X p, a₂, Y p, b] := by
          funext i
          fin_cases i <;> simp
        rw [harg, harg₁, harg₂] at h
        exact h)
      (fun c a b => by
        have h := hA.smul 1
          (![X p, 0, Y p, b] : Fin 4 → TangentSpace I p) c a
        have harg : Function.update
              (![X p, 0, Y p, b] : Fin 4 → TangentSpace I p) 1 (c • a) =
            ![X p, c • a, Y p, b] := by
          funext i
          fin_cases i <;> simp
        have harg' : Function.update
              (![X p, 0, Y p, b] : Fin 4 → TangentSpace I p) 1 a =
            ![X p, a, Y p, b] := by
          funext i
          fin_cases i <;> simp
        rw [harg, harg'] at h
        simpa [smul_eq_mul] using h)
      (fun a b₁ b₂ => by
        have h := hA.add 3
          (![X p, a, Y p, 0] : Fin 4 → TangentSpace I p) b₁ b₂
        have harg : Function.update
              (![X p, a, Y p, 0] : Fin 4 → TangentSpace I p) 3 (b₁ + b₂) =
            ![X p, a, Y p, b₁ + b₂] := by
          funext i
          fin_cases i <;> simp
        have harg₁ : Function.update
              (![X p, a, Y p, 0] : Fin 4 → TangentSpace I p) 3 b₁ =
            ![X p, a, Y p, b₁] := by
          funext i
          fin_cases i <;> simp
        have harg₂ : Function.update
              (![X p, a, Y p, 0] : Fin 4 → TangentSpace I p) 3 b₂ =
            ![X p, a, Y p, b₂] := by
          funext i
          fin_cases i <;> simp
        rw [harg, harg₁, harg₂] at h
        exact h)
      (fun c a b => by
        have h := hA.smul 3
          (![X p, a, Y p, 0] : Fin 4 → TangentSpace I p) c b
        have harg : Function.update
              (![X p, a, Y p, 0] : Fin 4 → TangentSpace I p) 3 (c • b) =
            ![X p, a, Y p, c • b] := by
          funext i
          fin_cases i <;> simp
        have harg' : Function.update
              (![X p, a, Y p, 0] : Fin 4 → TangentSpace I p) 3 b =
            ![X p, a, Y p, b] := by
          funext i
          fin_cases i <;> simp
        rw [harg, harg'] at h
        simpa [smul_eq_mul] using h)
  have hBfield (P Q : SmoothVectorField I M) :
      B (P p) (Q p) = A ![X, P, Y, Q] p := by
    dsimp [B]
    have h := pointwiseValue_eq hA.tensorial ![X, P, Y, Q]
    have harg : (![X p, P p, Y p, Q p] : Fin 4 → TangentSpace I p) =
        fun i => (![X, P, Y, Q] i) p := by
      funext i
      fin_cases i <;> rfl
    rw [harg]
    exact h
  have hframe :
      (∑ j, secondCovDerivAlong nabla U V (riemannTensorField g)
        ![X, F j, Y, F j] p) =
        ∑ j, B (e j) (e j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [he j]
    exact (hBfield (F j) (F j)).symm
  have hstd :
      (∑ j, B (stdOrthonormalBasis ℝ (TangentSpace I p) j)
        (stdOrthonormalBasis ℝ (TangentSpace I p) j)) =
        ∑ j, secondCovDerivAlong nabla U V (riemannTensorField g)
          ![X, MorganTianLib.extendVector p
              (stdOrthonormalBasis ℝ (TangentSpace I p) j), Y,
            MorganTianLib.extendVector p
              (stdOrthonormalBasis ℝ (TangentSpace I p) j)] p := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simpa [A, MorganTianLib.extendVector_apply] using
      (hBfield (MorganTianLib.extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) j))
        (MorganTianLib.extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) j)))
  calc
    secondCovDerivAlong g.leviCivitaConnection U V (ricciTensorField g)
          ![X, Y] p =
        ∑ j, secondCovDerivAlong nabla U V (riemannTensorField g)
          ![X, F j, Y, F j] p := by
            simpa [nabla, F] using
              (secondCovDerivAlong_ricciTensorField_eq_orthoFrame_sum
                g U V X Y p)
    _ = ∑ j, B (e j) (e j) := hframe
    _ = ∑ j, B (stdOrthonormalBasis ℝ (TangentSpace I p) j)
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) :=
      (OrthonormalBasis.sum_apply_diagonal_invariant
        (stdOrthonormalBasis ℝ (TangentSpace I p)) e B).symm
    _ = _ := hstd

#print axioms Topping.isPointwiseMultilinear_secondCovDerivAlong_riemannTensorField
#print axioms Topping.secondCovDerivAlong_ricciTensorField_eq_orthoFrame_sum
#print axioms Topping.secondCovDerivAlong_ricciTensorField_eq_stdOrthonormalBasis_sum

end Topping

end
