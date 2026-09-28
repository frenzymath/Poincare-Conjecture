import MorganTianLib.Ch01.RicciDivergence
import Topping.Riemannian.ConstantOfZeroDifferential
import Topping.Riemannian.Curvature

/-!
# Einstein metrics: constancy of the Einstein factor (Schur's lemma)

Topping's Chapter 2 observes that the two formulations of the Einstein condition
-- with a constant factor and with a function factor -- coincide when `n ≠ 2`: if
`Ric(g) = λ g` for a *function* `λ : M → ℝ`, then `λ` and the scalar curvature
are constant.

The proof is the contracted second Bianchi identity `dR = 2 δ(Ric)`, already
available as `MorganTianLib.dir_scalarCurvature_eq_two_divRicci`. Tracing
`Ric = λ g` gives `R = nλ`, and taking the divergence of `Ric = λ g` gives
`δ(Ric) = dλ`, hence `n dλ = dR = 2 δ(Ric) = 2 dλ`, so `(n - 2) dλ = 0`. For
`n ≠ 2` the differential of `λ` vanishes, and on a connected manifold `λ` is
constant.

The bridge lemmas identify Topping's Ricci and scalar curvature with the
Morgan--Tian ones, which is what makes the shared Bianchi infrastructure
applicable: both are `Riemannian.ricciForm` / `Riemannian.scalarCurvature`
applied to the same pointwise curvature form of the Levi-Civita connection.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [I.Boundaryless] in
/-- **Math.** The Levi-Civita hypothesis for the connection attached to a
Riemannian metric, in the form the shared curvature infrastructure expects. -/
theorem isLeviCivita_leviCivitaConnection (g : RiemannianMetric I M) :
    g.leviCivitaConnection.IsLeviCivita g :=
  g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y W q => g.koszulDualSection_dual X Y W q)

omit [I.Boundaryless] in
/-- **Math.** Topping's pointwise Riemann tensor is the shared pointwise
curvature form of the Levi-Civita connection. -/
theorem riemannCurvatureAt_eq_curvatureFormAt (g : RiemannianMetric I M) (p : M)
    (x y z w : TangentSpace I p) :
    riemannCurvatureAt g p x y z w =
      g.leviCivitaConnection.curvatureFormAt g p x y z w := rfl

/-- **Math.** Topping's pointwise Riemann tensor agrees with the Morgan--Tian
pointwise curvature form: both evaluate `⟨R(X,Y)Z,W⟩` on arbitrary smooth
extensions of the four tangent vectors, and the curvature `4`-tensor is
tensorial, so the choice of extension is immaterial. -/
theorem riemannCurvatureAt_eq_mtCurvatureFormAt (g : RiemannianMetric I M)
    (p : M) (x y z w : TangentSpace I p) :
    riemannCurvatureAt g p x y z w =
      MorganTianLib.curvatureFormAt g g.leviCivitaConnection p x y z w := by
  rw [MorganTianLib.curvatureFormAt_def,
    ← g.leviCivitaConnection.curvatureFormAt_eq g p
      (MorganTianLib.extendVector_apply p x) (MorganTianLib.extendVector_apply p y)
      (MorganTianLib.extendVector_apply p z) (MorganTianLib.extendVector_apply p w)]
  rfl

/-- **Math.** Topping's Ricci tensor agrees with the Morgan--Tian Ricci tensor:
both are the trace of the same pointwise curvature form. -/
theorem ricciTensorAt_eq_ricciAt (g : RiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    ricciTensorAt g p v w =
      MorganTianLib.ricciAt g g.leviCivitaConnection
        (isLeviCivita_leviCivitaConnection g) p v w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [ricciTensorAt_eq_sum g p v w (stdOrthonormalBasis ℝ (TangentSpace I p))]
  rw [MorganTianLib.ricciAt, Riemannian.ricciForm_eq_sum _ v w
    (stdOrthonormalBasis ℝ (TangentSpace I p))]
  exact Finset.sum_congr rfl fun i _ =>
    riemannCurvatureAt_eq_mtCurvatureFormAt g p v _ w _

/-- **Math.** Topping's scalar curvature agrees with the Morgan--Tian scalar
curvature. -/
theorem scalarCurvatureAt_eq_scalarCurvatureAt (g : RiemannianMetric I M)
    (p : M) :
    scalarCurvatureAt g p =
      MorganTianLib.scalarCurvatureAt g g.leviCivitaConnection
        (isLeviCivita_leviCivitaConnection g) p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [scalarCurvatureAt_eq_sum g p (stdOrthonormalBasis ℝ (TangentSpace I p)),
    MorganTianLib.scalarCurvatureAt,
    show MorganTianLib.scalarCurvature
        (MorganTianLib.isAlgCurvatureForm_curvatureFormAt g g.leviCivitaConnection
          (isLeviCivita_leviCivitaConnection g) p)
      = ∑ i, ∑ j, MorganTianLib.curvatureFormAt g g.leviCivitaConnection p
          (stdOrthonormalBasis ℝ (TangentSpace I p) i)
          (stdOrthonormalBasis ℝ (TangentSpace I p) j)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i)
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) from
      Riemannian.scalarCurvature_eq_sum _ (stdOrthonormalBasis ℝ (TangentSpace I p))]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    riemannCurvatureAt_eq_mtCurvatureFormAt g p _ _ _ _

/-- **Math.** The **contracted second Bianchi identity** in Topping's notation:
`dR = 2 δ(Ric)`, i.e. the derivative of the scalar curvature along any vector
field is twice the divergence of the Ricci tensor. -/
theorem dir_scalarCurvatureAt_eq_two_divRicci (g : RiemannianMetric I M)
    (U : SmoothVectorField I M) (p : M) :
    U.dir (fun q => scalarCurvatureAt g q) p =
      2 * MorganTianLib.divRicciAt g g.leviCivitaConnection
        (isLeviCivita_leviCivitaConnection g) p (U p) := by
  have hfun : (fun q => scalarCurvatureAt g q) =
      MorganTianLib.scalarCurvatureAt g g.leviCivitaConnection
        (isLeviCivita_leviCivitaConnection g) :=
    funext fun q => scalarCurvatureAt_eq_scalarCurvatureAt g q
  rw [hfun]
  exact MorganTianLib.dir_scalarCurvature_eq_two_divRicci g
    g.leviCivitaConnection (isLeviCivita_leviCivitaConnection g) U p

/-- **Math.** Topping's Einstein condition with a **function** factor:
`Ric(g) = λ g` for `λ : M → ℝ`. -/
def IsEinsteinWithFactor (g : RiemannianMetric I M) (lam : M → ℝ) : Prop :=
  ∀ (p : M) (v w : TangentSpace I p),
    ricciTensorAt g p v w = lam p * g.metricInner p v w

/-- **Math.** Tracing `Ric = λ g` gives `R = nλ`, where `n = dim M`. -/
theorem scalarCurvatureAt_eq_finrank_mul_of_isEinsteinWithFactor
    (g : RiemannianMetric I M) {lam : M → ℝ}
    (h : IsEinsteinWithFactor g lam) (p : M) :
    scalarCurvatureAt g p = (Module.finrank ℝ E : ℝ) * lam p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hsum := scalarCurvatureAt_eq_trace g p
  rw [hsum, Riemannian.bilinTrace_eq_sum _ (stdOrthonormalBasis ℝ (TangentSpace I p))]
  have hone : ∀ i, ricciTensorAt g p (stdOrthonormalBasis ℝ (TangentSpace I p) i)
      (stdOrthonormalBasis ℝ (TangentSpace I p) i) = lam p := by
    intro i
    rw [h p]
    have hnorm : g.metricInner p (stdOrthonormalBasis ℝ (TangentSpace I p) i)
        (stdOrthonormalBasis ℝ (TangentSpace I p) i) = 1 := by
      have h1 : inner ℝ (stdOrthonormalBasis ℝ (TangentSpace I p) i)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) = 1 := by
        have := orthonormal_iff_ite.mp
          (stdOrthonormalBasis ℝ (TangentSpace I p)).orthonormal i i
        rwa [if_pos rfl] at this
      exact h1
    rw [hnorm, mul_one]
  rw [Finset.sum_congr rfl fun i _ => hone i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  simp only [nsmul_eq_mul]
  congr 1

/-- **Math.** The covariant derivative of `Ric = λ g` is `dλ ⊗ g`: metric
compatibility kills the derivative of `g`, leaving only the derivative of the
factor. The smoothness of `λ` is a hypothesis because `IsEinsteinWithFactor`
constrains `λ` only through the pointwise identity `Ric = λ g`. -/
theorem covRicci_of_isEinsteinWithFactor (g : RiemannianMetric I M)
    {lam : M → ℝ} (hlam : MDifferentiable I 𝓘(ℝ, ℝ) lam)
    (h : IsEinsteinWithFactor g lam)
    (U X Y : SmoothVectorField I M) (p : M) :
    MorganTianLib.covRicci g g.leviCivitaConnection
        (isLeviCivita_leviCivitaConnection g) U X Y p =
      U.dir lam p * g.metricInner p (X p) (Y p) := by
  have hcompat := (isLeviCivita_leviCivitaConnection g).2
  have hricXY : ∀ (A B : SmoothVectorField I M) (q : M),
      MorganTianLib.ricciField g g.leviCivitaConnection
        (isLeviCivita_leviCivitaConnection g) A B q
      = lam q * g.metricInner q (A q) (B q) := by
    intro A B q
    rw [MorganTianLib.ricciField, ← ricciTensorAt_eq_ricciAt, h q]
  have hric : MorganTianLib.ricciField g g.leviCivitaConnection
      (isLeviCivita_leviCivitaConnection g) X Y
      = fun q => lam q * g.metricInner q (X q) (Y q) :=
    funext fun q => hricXY X Y q
  -- Differentiate the product `λ · ⟨X,Y⟩` and expand `U⟨X,Y⟩` by compatibility.
  have hprod : U.dir (fun q => lam q * g.metricInner q (X q) (Y q)) p
      = lam p * U.dir (fun q => g.metricInner q (X q) (Y q)) p
        + g.metricInner p (X p) (Y p) * U.dir lam p :=
    U.dir_mul p (hlam p)
      (g.metricInner_field_mdifferentiableAt X Y p)
  rw [MorganTianLib.covRicci, hric, hprod, hricXY, hricXY,
    hcompat U X Y p]
  ring

/-- **Math.** Pointwise form: for `Ric = λ g`, `(∇_u Ric)(v,w) = dλ(u)⟨v,w⟩`. -/
theorem covRicciAt_of_isEinsteinWithFactor (g : RiemannianMetric I M)
    {lam : M → ℝ} (hlam : MDifferentiable I 𝓘(ℝ, ℝ) lam)
    (h : IsEinsteinWithFactor g lam) (p : M) (u v w : TangentSpace I p) :
    MorganTianLib.covRicciAt g g.leviCivitaConnection
        (isLeviCivita_leviCivitaConnection g) p u v w =
      dirTangent lam u * g.metricInner p v w := by
  rw [MorganTianLib.covRicciAt,
    covRicci_of_isEinsteinWithFactor g hlam h _ _ _ p]
  simp only [MorganTianLib.extendVector_apply, SmoothVectorField.dir, dirTangent]

/-- **Math.** For `Ric = λ g`, the divergence of the Ricci tensor is `dλ`:
tracing `∇Ric = dλ ⊗ g` over an orthonormal basis leaves `dλ`. -/
theorem divRicciAt_of_isEinsteinWithFactor (g : RiemannianMetric I M)
    {lam : M → ℝ} (hlam : MDifferentiable I 𝓘(ℝ, ℝ) lam)
    (h : IsEinsteinWithFactor g lam) (p : M) (w : TangentSpace I p) :
    MorganTianLib.divRicciAt g g.leviCivitaConnection
        (isLeviCivita_leviCivitaConnection g) p w =
      dirTangent lam w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with he
  rw [MorganTianLib.divRicciAt_eq_sum_orthonormalBasis _ _ _ p w e,
    Finset.sum_congr rfl fun i _ =>
      covRicciAt_of_isEinsteinWithFactor g hlam h p (e i) (e i) w]
  -- `dλ` is linear, and `Σᵢ ⟨eᵢ,w⟩ • eᵢ = w`.
  have hexp : ∑ i, (g.metricInner p (e i) w) • (e i : TangentSpace I p) = w := by
    have hcoef : ∀ i, (g.metricInner p (e i) w) • (e i : TangentSpace I p)
        = (e.repr w).ofLp i • e i := by
      intro i
      rw [e.repr_apply_apply w i]
      rfl
    rw [Finset.sum_congr rfl fun i _ => hcoef i]
    exact e.sum_repr w
  calc ∑ i, dirTangent lam (e i) * g.metricInner p (e i) w
      = ∑ i, dirTangent lam ((g.metricInner p (e i) w) • (e i : TangentSpace I p)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [dirTangent_smul]
        ring
    _ = dirTangent lam (∑ i, (g.metricInner p (e i) w) • (e i : TangentSpace I p)) := by
        simp only [dirTangent]
        exact (map_sum (mfderiv I 𝓘(ℝ, ℝ) lam p) _ _).symm
    _ = dirTangent lam w := by rw [hexp]

/-- **Math.** **Schur's identity.** For `Ric = λ g`, the contracted second
Bianchi identity forces `(n - 2) dλ = 0`: tracing gives `R = nλ` so
`dR = n dλ`, while `dR = 2 δ(Ric) = 2 dλ`. -/
theorem finrank_sub_two_mul_dirTangent_lam_eq_zero (g : RiemannianMetric I M)
    {lam : M → ℝ} (hlam : MDifferentiable I 𝓘(ℝ, ℝ) lam)
    (h : IsEinsteinWithFactor g lam) (U : SmoothVectorField I M) (p : M) :
    ((Module.finrank ℝ E : ℝ) - 2) * U.dir lam p = 0 := by
  -- `dR = n dλ` from `R = nλ`.
  have hscal : (fun q => scalarCurvatureAt g q)
      = fun q => (Module.finrank ℝ E : ℝ) * lam q :=
    funext fun q =>
      scalarCurvatureAt_eq_finrank_mul_of_isEinsteinWithFactor g h q
  have hleft : U.dir (fun q => scalarCurvatureAt g q) p
      = (Module.finrank ℝ E : ℝ) * U.dir lam p := by
    rw [hscal]
    have hconst : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun _ : M => (Module.finrank ℝ E : ℝ)) p :=
      mdifferentiableAt_const
    rw [U.dir_mul p hconst (hlam p)]
    have hzero : U.dir (fun _ : M => (Module.finrank ℝ E : ℝ)) p = 0 := by
      simp only [SmoothVectorField.dir, mfderiv_const]
      rfl
    rw [hzero, mul_zero, add_zero]
  -- `dR = 2 δ(Ric) = 2 dλ` from the contracted second Bianchi identity.
  have hright : U.dir (fun q => scalarCurvatureAt g q) p = 2 * U.dir lam p := by
    rw [dir_scalarCurvatureAt_eq_two_divRicci g U p,
      divRicciAt_of_isEinsteinWithFactor g hlam h p (U p)]
    rfl
  have := hleft.symm.trans hright
  linarith [this]

/-- **Math.** **Constancy of the Einstein factor** (Topping Ch. 2, Schur's
lemma). If `Ric(g) = λ g` for a function `λ : M → ℝ` and `n ≠ 2`, then the
differential of `λ` vanishes identically, and hence so does that of the scalar
curvature: both are constant on a connected manifold. -/
theorem dirTangent_lam_eq_zero_of_isEinsteinWithFactor (g : RiemannianMetric I M)
    (hn : Module.finrank ℝ E ≠ 2) {lam : M → ℝ}
    (hlam : MDifferentiable I 𝓘(ℝ, ℝ) lam) (h : IsEinsteinWithFactor g lam)
    (U : SmoothVectorField I M) (p : M) :
    U.dir lam p = 0 := by
  have hne : ((Module.finrank ℝ E : ℝ) - 2) ≠ 0 := by
    intro hcontra
    have : (Module.finrank ℝ E : ℝ) = 2 := by linarith
    exact hn (by exact_mod_cast this)
  have h0 := finrank_sub_two_mul_dirTangent_lam_eq_zero g hlam h U p
  exact (mul_eq_zero.mp h0).resolve_left hne

/-- **Math.** The differential of `λ` vanishes as a covector at every point, the
basis-free form of `dirTangent_lam_eq_zero_of_isEinsteinWithFactor`. -/
theorem mfderiv_lam_eq_zero_of_isEinsteinWithFactor (g : RiemannianMetric I M)
    (hn : Module.finrank ℝ E ≠ 2) {lam : M → ℝ}
    (hlam : MDifferentiable I 𝓘(ℝ, ℝ) lam) (h : IsEinsteinWithFactor g lam)
    (p : M) : mfderiv I 𝓘(ℝ, ℝ) lam p = 0 := by
  ext v
  obtain ⟨U, hU⟩ := Riemannian.exists_smoothVectorField_eq p v
  have h0 := dirTangent_lam_eq_zero_of_isEinsteinWithFactor g hn hlam h U p
  rw [SmoothVectorField.dir, hU] at h0
  exact h0

/-- **Math.** Constancy of the scalar curvature reduces to constancy of the
factor: `R = nλ`, so `λ` constant gives `R` constant. -/
theorem scalarCurvature_const_of_lam_const (g : RiemannianMetric I M)
    {lam : M → ℝ} (h : IsEinsteinWithFactor g lam)
    (hconst : ∀ p q : M, lam p = lam q) (p q : M) :
    scalarCurvatureAt g p = scalarCurvatureAt g q := by
  rw [scalarCurvatureAt_eq_finrank_mul_of_isEinsteinWithFactor g h p,
    scalarCurvatureAt_eq_finrank_mul_of_isEinsteinWithFactor g h q,
    hconst p q]

/-- **Math.** Under the same hypotheses the scalar curvature has vanishing
differential, so it is constant on a connected manifold. -/
theorem dir_scalarCurvatureAt_eq_zero_of_isEinsteinWithFactor
    (g : RiemannianMetric I M) (hn : Module.finrank ℝ E ≠ 2) {lam : M → ℝ}
    (hlam : MDifferentiable I 𝓘(ℝ, ℝ) lam) (h : IsEinsteinWithFactor g lam)
    (U : SmoothVectorField I M) (p : M) :
    U.dir (fun q => scalarCurvatureAt g q) p = 0 := by
  rw [dir_scalarCurvatureAt_eq_two_divRicci g U p,
    divRicciAt_of_isEinsteinWithFactor g hlam h p (U p)]
  have h0 := dirTangent_lam_eq_zero_of_isEinsteinWithFactor g hn hlam h U p
  rw [show dirTangent lam (U p) = U.dir lam p from rfl, h0, mul_zero]

/-! ### The smoothness of the factor is not an extra hypothesis

`IsEinsteinWithFactor g lam` pins `lam` down: tracing gives `R = nλ`, so
`λ = R/n`, and the scalar curvature is differentiable unconditionally. So the
smoothness of `λ` that the intermediate lemmas assume is *derivable*, and the
headline statements below take no such hypothesis. -/

/-- **Math.** `λ = R/n` is forced by `Ric = λ g`, by tracing. -/
theorem lam_eq_scalarCurvatureAt_div (g : RiemannianMetric I M) {lam : M → ℝ}
    (h : IsEinsteinWithFactor g lam) :
    lam = fun q => scalarCurvatureAt g q / (Module.finrank ℝ E : ℝ) := by
  have hn : ((Module.finrank ℝ E : ℝ)) ≠ 0 := by
    have : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
    positivity
  funext q
  rw [scalarCurvatureAt_eq_finrank_mul_of_isEinsteinWithFactor g h q]
  field_simp

/-- **Math.** The Einstein factor is differentiable: it is `R/n`, and the scalar
curvature is differentiable. -/
theorem mdifferentiable_lam_of_isEinsteinWithFactor (g : RiemannianMetric I M)
    {lam : M → ℝ} (h : IsEinsteinWithFactor g lam) :
    MDifferentiable I 𝓘(ℝ, ℝ) lam := by
  have hsmul : lam = ((Module.finrank ℝ E : ℝ))⁻¹ •
      fun q => scalarCurvatureAt g q := by
    rw [lam_eq_scalarCurvatureAt_div g h]
    funext q
    simp [div_eq_inv_mul]
  rw [hsmul]
  intro q
  have hscal : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun r => scalarCurvatureAt g r) q := by
    have hfun : (fun r => scalarCurvatureAt g r)
        = MorganTianLib.scalarCurvatureAt g g.leviCivitaConnection
            (isLeviCivita_leviCivitaConnection g) :=
      funext fun r => scalarCurvatureAt_eq_scalarCurvatureAt g r
    rw [hfun]
    exact MorganTianLib.scalarCurvatureAt_mdifferentiableAt g
      g.leviCivitaConnection (isLeviCivita_leviCivitaConnection g) q
  exact hscal.const_smul _

/-! ### Schur's lemma, with the connectedness step supplied

Topping's proposition asserts that `λ` and `R` *are constant*. The identity
`(n-2)dλ = 0` only gives the vanishing of a differential; constancy is the
connectedness argument, now available as
`Topping.apply_eq_of_mfderiv_eq_zero`. -/

/-- **Math.** The Einstein factor is **constant** on a connected manifold: its
differential vanishes by Schur's identity, and a real function with vanishing
differential on a preconnected manifold is constant. -/
theorem lam_const_of_isEinsteinWithFactor [PreconnectedSpace M]
    (g : RiemannianMetric I M) (hn : Module.finrank ℝ E ≠ 2) {lam : M → ℝ}
    (hlam : MDifferentiable I 𝓘(ℝ, ℝ) lam) (h : IsEinsteinWithFactor g lam)
    (p q : M) : lam p = lam q :=
  apply_eq_of_mfderiv_eq_zero (hlam)
    (fun x => mfderiv_lam_eq_zero_of_isEinsteinWithFactor g hn hlam h x) p q

/-- **Math.** **Topping's Chapter 2 proposition, in full.** If `Ric(g) = λ g` for
a function `λ` and `n ≠ 2`, then on a connected manifold both `λ` and the scalar
curvature are constant — so the constant-factor and function-factor formulations
of the Einstein condition coincide in these dimensions.

This is the statement the blueprint node makes: constancy, not merely vanishing
differentials. The two halves are Schur's identity `(n-2)dλ = 0` and the
connectedness argument; `R = nλ` transports constancy from `λ` to `R`. -/
theorem scalarCurvatureAt_const_of_isEinsteinWithFactor [PreconnectedSpace M]
    (g : RiemannianMetric I M) (hn : Module.finrank ℝ E ≠ 2) {lam : M → ℝ}
    (hlam : MDifferentiable I 𝓘(ℝ, ℝ) lam) (h : IsEinsteinWithFactor g lam)
    (p q : M) : scalarCurvatureAt g p = scalarCurvatureAt g q :=
  scalarCurvature_const_of_lam_const g h
    (fun x y => lam_const_of_isEinsteinWithFactor g hn hlam h x y) p q

/-! ### Without the smoothness hypothesis

The two statements above carry `hlam` because their intermediate lemmas do. It is
not a real hypothesis: `λ = R/n` is forced by `Ric = λ g`, and `R` is
differentiable unconditionally. The versions below therefore state Topping's
proposition with no smoothness assumption on `λ` at all — only the Einstein
condition, `n ≠ 2`, and connectedness, which is exactly the book's hypothesis
set. -/

/-- **Math.** The differential of the Einstein factor vanishes, with no smoothness
hypothesis: differentiability of `λ` is derived from `λ = R/n`. -/
theorem mfderiv_lam_eq_zero_of_isEinsteinWithFactor'
    (g : RiemannianMetric I M) (hn : Module.finrank ℝ E ≠ 2) {lam : M → ℝ}
    (h : IsEinsteinWithFactor g lam) (p : M) :
    mfderiv I 𝓘(ℝ, ℝ) lam p = 0 :=
  mfderiv_lam_eq_zero_of_isEinsteinWithFactor g hn
    (mdifferentiable_lam_of_isEinsteinWithFactor g h) h p

/-- **Math.** **Topping's proposition with the book's hypotheses exactly.** On a
connected manifold, `Ric(g) = λ g` with `n ≠ 2` forces `λ` and the scalar
curvature to be constant — no smoothness assumption on `λ`. -/
theorem lam_const_of_isEinsteinWithFactor' [PreconnectedSpace M]
    (g : RiemannianMetric I M) (hn : Module.finrank ℝ E ≠ 2) {lam : M → ℝ}
    (h : IsEinsteinWithFactor g lam) (p q : M) : lam p = lam q :=
  apply_eq_of_mfderiv_eq_zero (mdifferentiable_lam_of_isEinsteinWithFactor g h)
    (fun x => mfderiv_lam_eq_zero_of_isEinsteinWithFactor' g hn h x) p q

/-- **Math.** The scalar curvature is constant under the book's hypotheses. -/
theorem scalarCurvatureAt_const_of_isEinsteinWithFactor' [PreconnectedSpace M]
    (g : RiemannianMetric I M) (hn : Module.finrank ℝ E ≠ 2) {lam : M → ℝ}
    (h : IsEinsteinWithFactor g lam) (p q : M) :
    scalarCurvatureAt g p = scalarCurvatureAt g q :=
  scalarCurvature_const_of_lam_const g h
    (fun x y => lam_const_of_isEinsteinWithFactor' g hn h x y) p q

end Topping

end
