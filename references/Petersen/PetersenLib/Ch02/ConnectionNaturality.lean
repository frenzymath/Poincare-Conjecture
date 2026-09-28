import PetersenLib.Ch02.Connections
import PetersenLib.Ch01.RiemannianManifolds
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.12(1): naturality of the Levi-Civita
connection under isometries

For a Riemannian isometry `Φ : (M, g) → (M', g')` (a diffeomorphism preserving
the metric) the Levi-Civita connection is **natural**: the pushforward of a
covariant derivative is the covariant derivative of the pushforwards,
`Φ_*(∇^g_Y X) = ∇^{g'}_{Φ_*Y}(Φ_*X)` (`exercise2_5_12_naturality`, Petersen
Ex. 2.5.12(1)).

The proof is Koszul-driven and builds **no** pushforward connection. Both sides,
tested against the metric, satisfy Koszul's formula
`2 g(∇_Y X, Z) = koszulExpression g X Y Z` (`RiemannianConnection.koszul`), and
the six-term `koszulExpression` is itself natural under `Φ`
(`koszulExpression_pushforwardVF`), because each ingredient transports:

* the metric pairing (`metricInner_pushforwardVF`, from `PreservesMetric`);
* the directional derivative of a metric function (`directionalDerivative_pushforwardVF`,
  the chain rule);
* the Lie bracket (`pushforwardVF_lieBracket`, mathlib's `mpullback_mlieBracket`).

Since `DΦ_p` is a linear isomorphism, the metric test vector ranges over all of
`T_{Φp}M'` as `Φ_*Z`, so nondegeneracy (`metricInner_eq_iff_eq`) closes the
argument. The pushforward of a vector field is realized as the mathlib pullback
along `Φ.symm` (`pushforwardVF`), whose value at `Φp` is `DΦ_p(X|_p)`
(`pushforwardVF_apply`).

This is also the connection-naturality lemma needed for the geodesic-mapping /
exponential-naturality half of Petersen §5.6.1.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercise 2.5.12.
-/

open Bundle Set Function Finset VectorField
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [InnerProductSpace ℝ E']
  [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-! ## The differential of a diffeomorphism as a linear equivalence -/

section MFDerivEquiv

/-- The differential of `Φ.symm` is a left inverse of the differential of `Φ`. -/
private theorem mfderiv_symm_leftInverse (Φ : Diffeomorph I I' M M' ∞) (x : M) :
    Function.LeftInverse (mfderiv I' I Φ.symm (Φ x)) (mfderiv I I' Φ x) := by
  intro v
  have h := mfderiv_comp x (Φ.symm.contMDiff.mdifferentiableAt (by decide) (x := Φ x))
    (Φ.contMDiff.mdifferentiableAt (by decide) (x := x))
  have hid : (⇑Φ.symm ∘ ⇑Φ) = (id : M → M) := funext fun a => Φ.symm_apply_apply a
  rw [hid, mfderiv_id] at h
  have := congrArg (fun L => L v) h
  simpa using! this.symm

/-- The differential of `Φ` is a left inverse of the differential of `Φ.symm`. -/
private theorem mfderiv_symm_rightInverse (Φ : Diffeomorph I I' M M' ∞) (x : M) :
    Function.RightInverse (mfderiv I' I Φ.symm (Φ x)) (mfderiv I I' Φ x) := by
  intro w
  have h := mfderiv_comp (Φ x) (Φ.contMDiff.mdifferentiableAt (by decide) (x := Φ.symm (Φ x)))
    (Φ.symm.contMDiff.mdifferentiableAt (by decide) (x := Φ x))
  have hid : (⇑Φ ∘ ⇑Φ.symm) = (id : M' → M') := funext fun a => Φ.apply_symm_apply a
  rw [hid, mfderiv_id] at h
  rw [Φ.symm_apply_apply] at h
  have := congrArg (fun L => L w) h
  simpa using! this.symm

/-- **Math.** The differential `DΦ_x : T_xM → T_{Φx}M'` of a diffeomorphism,
packaged as a continuous linear equivalence with inverse `DΦ⁻¹_{Φx}`. -/
def mfderivEquiv (Φ : Diffeomorph I I' M M' ∞) (x : M) :
    TangentSpace I x ≃L[ℝ] TangentSpace I' (Φ x) :=
  ContinuousLinearEquiv.equivOfInverse (mfderiv I I' Φ x) (mfderiv I' I Φ.symm (Φ x))
    (mfderiv_symm_leftInverse Φ x) (mfderiv_symm_rightInverse Φ x)

@[simp] theorem mfderivEquiv_apply (Φ : Diffeomorph I I' M M' ∞) (x : M)
    (v : TangentSpace I x) : mfderivEquiv Φ x v = mfderiv I I' Φ x v :=
  ContinuousLinearEquiv.equivOfInverse_apply _ _ _ _ v

theorem mfderivEquiv_coe (Φ : Diffeomorph I I' M M' ∞) (x : M) :
    (mfderivEquiv Φ x : TangentSpace I x →L[ℝ] TangentSpace I' (Φ x)) = mfderiv I I' Φ x :=
  ContinuousLinearMap.ext fun v => mfderivEquiv_apply Φ x v

/-- **Math.** The differential of a diffeomorphism is invertible at every point. -/
theorem mfderiv_diffeomorph_isInvertible (Φ : Diffeomorph I I' M M' ∞) (x : M) :
    (mfderiv I I' Φ x).IsInvertible :=
  ⟨mfderivEquiv Φ x, mfderivEquiv_coe Φ x⟩

end MFDerivEquiv

/-! ## Pushforward of a vector field -/

/-- **Math.** The **pushforward** of a vector field `X` on `M` under a
diffeomorphism `Φ`, realized as the mathlib pullback along `Φ.symm`. Petersen's
`(Φ_*X)|_q = DΦ(X|_{Φ⁻¹(q)})`. -/
def pushforwardVF (Φ : Diffeomorph I I' M M' ∞) (X : Π x : M, TangentSpace I x) :
    Π q : M', TangentSpace I' q :=
  VectorField.mpullback I' I Φ.symm X

/-- **Math.** The value bridge: `(Φ_*X)|_{Φp} = DΦ_p(X|_p)`. -/
theorem pushforwardVF_apply (Φ : Diffeomorph I I' M M' ∞)
    (X : Π x : M, TangentSpace I x) (p : M) :
    pushforwardVF Φ X (Φ p) = mfderiv I I' Φ p (X p) := by
  have hI : (mfderiv I' I ⇑Φ.symm (Φ p)).IsInvertible :=
    mfderiv_diffeomorph_isInvertible Φ.symm (Φ p)
  have key : (mfderiv I' I ⇑Φ.symm (Φ p)).inverse (X p) = mfderiv I I' ⇑Φ p (X p) := by
    conv_lhs => rw [← mfderiv_symm_leftInverse Φ p (X p)]
    exact hI.inverse_apply_self _
  simp only [pushforwardVF, mpullback]
  rw [Φ.symm_apply_apply]
  exact key

/-- **Math.** The pushforward of a smooth vector field is smooth. -/
theorem pushforwardVF_isSmooth (Φ : Diffeomorph I I' M M' ∞)
    {X : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X) :
    IsSmoothVectorField (pushforwardVF Φ X) := by
  refine ContMDiff.mpullback_vectorField (I := I') (I' := I) (f := ⇑Φ.symm)
    hX Φ.symm.contMDiff (fun x => mfderiv_diffeomorph_isInvertible Φ.symm x) ?_
  simp

/-! ## Naturality of the ingredients -/

variable {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'}

/-- **Math.** The metric pairing transports: for an isometry `Φ`,
`g'(DΦ u, DΦ v)|_{Φp} = g(u, v)|_p`. -/
theorem metricInner_pushforwardVF (Φ : Diffeomorph I I' M M' ∞)
    (hiso : PreservesMetric g g' Φ) (p : M) (u v : TangentSpace I p) :
    g'.metricInner (Φ p) (mfderiv I I' Φ p u) (mfderiv I I' Φ p v) = g.metricInner p u v :=
  (hiso p u v).symm

/-- **Math.** The directional derivative of a function transports under the
pushforward: `D_{Φ_*Y}(h)|_{Φp} = D_Y(h ∘ Φ)|_p` (the chain rule). -/
theorem directionalDerivative_pushforwardVF (Φ : Diffeomorph I I' M M' ∞)
    (Y : Π x : M, TangentSpace I x) (h : M' → ℝ) (p : M) :
    directionalDerivative (pushforwardVF Φ Y) h (Φ p)
      = directionalDerivative Y (h ∘ Φ) p := by
  have hΦ : MDifferentiableAt I I' Φ p := Φ.contMDiff.mdifferentiableAt (by decide)
  rw [directionalDerivative, directionalDerivative, pushforwardVF_apply]
  by_cases hh : MDifferentiableAt I' 𝓘(ℝ) h (Φ p)
  · rw [mfderiv_comp p hh hΦ]; rfl
  · have hnc : ¬ MDifferentiableAt I 𝓘(ℝ) (h ∘ Φ) p := by
      intro hc
      apply hh
      have hΦs : MDifferentiableAt I' I Φ.symm (Φ p) :=
        Φ.symm.contMDiff.mdifferentiableAt (by decide)
      have hc' : MDifferentiableAt I 𝓘(ℝ) (h ∘ ⇑Φ) (Φ.symm (Φ p)) := by
        rwa [Φ.symm_apply_apply]
      have hcomp : MDifferentiableAt I' 𝓘(ℝ) ((h ∘ ⇑Φ) ∘ ⇑Φ.symm) (Φ p) :=
        hc'.comp (Φ p) hΦs
      have heq : ((h ∘ ⇑Φ) ∘ ⇑Φ.symm) = h :=
        funext fun q => by simp [Function.comp, Φ.apply_symm_apply]
      rwa [heq] at hcomp
    rw [mfderiv_zero_of_not_mdifferentiableAt hh,
      mfderiv_zero_of_not_mdifferentiableAt hnc]
    rfl

/-- **Math.** The Lie bracket transports under the pushforward:
`Φ_*[X, Y] = [Φ_*X, Φ_*Y]` (mathlib's `mpullback_mlieBracket`). -/
theorem pushforwardVF_lieBracket (Φ : Diffeomorph I I' M M' ∞)
    {X Y : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    (hY : IsSmoothVectorField Y) :
    pushforwardVF Φ (lieDerivativeVectorField I X Y)
      = lieDerivativeVectorField I' (pushforwardVF Φ X) (pushforwardVF Φ Y) := by
  haveI hmM : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  haveI hmM' : IsManifold I' (minSmoothness ℝ 2) M' := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have hn : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top
  funext q
  simp only [lieDerivativeVectorField_eq_mlieBracket, pushforwardVF]
  exact mpullback_mlieBracket (I := I') (I' := I) (f := ⇑Φ.symm) (n := ∞)
    (hX.mdifferentiableAt (by decide)) (hY.mdifferentiableAt (by decide))
    (Φ.symm.contMDiff.contMDiffAt) hn

/-- **Math.** The six-term `koszulExpression` is natural under an isometry:
`koszulExpression g' (Φ_*X)(Φ_*Y)(Φ_*Z)|_{Φp} = koszulExpression g X Y Z|_p`. Each
of the six ingredients (three metric-function directional derivatives, three
bracket pairings) transports by `directionalDerivative_pushforwardVF`,
`metricInner_pushforwardVF`, and `pushforwardVF_lieBracket`. -/
theorem koszulExpression_pushforwardVF (Φ : Diffeomorph I I' M M' ∞)
    (hiso : PreservesMetric g g' Φ) {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (p : M) :
    koszulExpression g' (pushforwardVF Φ X) (pushforwardVF Φ Y) (pushforwardVF Φ Z) (Φ p)
      = koszulExpression g X Y Z p := by
  have hmf : ∀ A B : Π x : M, TangentSpace I x,
      (fun q => g'.metricInner q (pushforwardVF Φ A q) (pushforwardVF Φ B q)) ∘ ⇑Φ
        = fun r => g.metricInner r (A r) (B r) := by
    intro A B; funext r
    simp only [Function.comp_apply, pushforwardVF_apply]
    exact metricInner_pushforwardVF Φ hiso r (A r) (B r)
  have hbr : ∀ A B C : Π x : M, TangentSpace I x,
      IsSmoothVectorField A → IsSmoothVectorField B →
      g'.metricInner (Φ p)
          (lieDerivativeVectorField I' (pushforwardVF Φ A) (pushforwardVF Φ B) (Φ p))
          (pushforwardVF Φ C (Φ p))
        = g.metricInner p (lieDerivativeVectorField I A B p) (C p) := by
    intro A B C hA hB
    rw [← pushforwardVF_lieBracket Φ hA hB, pushforwardVF_apply, pushforwardVF_apply]
    exact metricInner_pushforwardVF Φ hiso p _ _
  unfold koszulExpression
  rw [directionalDerivative_pushforwardVF, directionalDerivative_pushforwardVF,
    directionalDerivative_pushforwardVF, hmf, hmf, hmf,
    hbr X Y Z hX hY, hbr Y Z X hY hZ, hbr Z X Y hZ hX]

/-- **Math.** **Exercise 2.5.12(1)** (Petersen, §2.5): the Levi-Civita connection
is **natural under a Riemannian isometry** `Φ : (M, g) → (M', g')`:
`Φ_*(∇^g_Y X) = ∇^{g'}_{Φ_*Y}(Φ_*X)`. Both sides satisfy Koszul's formula, whose
right-hand side is natural under `Φ` (`koszulExpression_pushforwardVF`); since
`DΦ_p` is a linear isomorphism the metric test vector ranges over all of
`T_{Φp}M'` as `Φ_*Z`, so nondegeneracy of `g'` forces equality. -/
theorem exercise2_5_12_naturality [I.Boundaryless] [CompleteSpace E]
    [SigmaCompactSpace M] [T2Space M] [I'.Boundaryless] [CompleteSpace E']
    [SigmaCompactSpace M'] [T2Space M']
    (Φ : Diffeomorph I I' M M' ∞) (hiso : PreservesMetric g g' Φ)
    {X Y : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    (hY : IsSmoothVectorField Y) :
    pushforwardVF Φ (fun p => g.leviCivita.cov p (Y p) X)
      = fun q => g'.leviCivita.cov q (pushforwardVF Φ Y q) (pushforwardVF Φ X) := by
  funext q
  obtain ⟨p, rfl⟩ : ∃ p, Φ p = q := ⟨Φ.symm q, Φ.apply_symm_apply q⟩
  refine (g'.metricInner_eq_iff_eq (Φ p) _ _).mp fun W => ?_
  -- represent the test vector `W` as `Φ_*Z` for a smooth field `Z`
  obtain ⟨Z, hZp⟩ := exists_smoothVectorField_eq (I := I) p (mfderiv I' I Φ.symm (Φ p) W)
  have hZsm : IsSmoothVectorField (⇑Z) := Z.smooth
  have hWZ : W = pushforwardVF Φ (⇑Z) (Φ p) := by
    rw [pushforwardVF_apply, hZp]
    exact (mfderiv_symm_rightInverse Φ p W).symm
  rw [hWZ]
  refine mul_left_cancel₀ (two_ne_zero) ?_
  have hpfX := pushforwardVF_isSmooth Φ hX
  have hpfY := pushforwardVF_isSmooth Φ hY
  have hpfZ := pushforwardVF_isSmooth Φ hZsm
  have htrans : g'.metricInner (Φ p)
      (pushforwardVF Φ (fun r => g.leviCivita.cov r (Y r) X) (Φ p))
      (pushforwardVF Φ (⇑Z) (Φ p))
      = g.metricInner p (g.leviCivita.cov p (Y p) X) (⇑Z p) := by
    rw [pushforwardVF_apply, pushforwardVF_apply]
    exact metricInner_pushforwardVF Φ hiso p _ _
  rw [htrans, RiemannianConnection.koszul g.leviCivita hX hY hZsm p,
    RiemannianConnection.koszul g'.leviCivita hpfX hpfY hpfZ (Φ p),
    koszulExpression_pushforwardVF Φ hiso hX hY hZsm p]

end PetersenLib

end
