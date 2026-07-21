import PetersenLib.Ch03.ProductMetricFacts
import PetersenLib.Ch03.ProductBracketFactor

open Bundle Set Function
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

section Smoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The pointwise inner product of two smooth vector fields is a smooth function. -/
theorem mdifferentiable_metricInner_of_smooth {g : RiemannianMetric I M}
    {V W : Π x : M, TangentSpace I x} (hV : IsSmoothVectorField V) (hW : IsSmoothVectorField W) :
    MDifferentiable I 𝓘(ℝ) (fun q => g.metricInner q (V q) (W q)) := by
  intro x
  have h := g.metricInner_contMDiffWithinAt (v := V) (w := W) (s := Set.univ) (x := x) (n := ∞)
    ((hV x).contMDiffWithinAt) ((hW x).contMDiffWithinAt)
  rw [contMDiffWithinAt_univ] at h
  exact h.mdifferentiableAt (by simp)

end Smoothness

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NeZero (Module.finrank ℝ E₁)] [CompleteSpace E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [I₁.Boundaryless]
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [SigmaCompactSpace M₁] [T2Space M₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NeZero (Module.finrank ℝ E₂)] [CompleteSpace E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂} [I₂.Boundaryless]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [SigmaCompactSpace M₂] [T2Space M₂]


variable (g₁ : RiemannianMetric I₁ M₁) (g₂ : RiemannianMetric I₂ M₂)

/-- **Lemma A (modulo the bracket facts).** `∇_{liftFst U}(liftSnd W) = 0` for the Levi-Civita
connection of a product metric.

The proof is Koszul's formula tested against a first-factor lift and against a second-factor lift;
each of the six Koszul terms dies, for the reason catalogued inline. Nondegeneracy
(`eq_zero_of_metricInner_prod_split`) then upgrades "orthogonal to every lift" to "zero". -/
theorem cov_liftFst_liftSnd_eq_zero_of_brackets
    {U : Π x : M₁, TangentSpace I₁ x} {W : Π x : M₂, TangentSpace I₂ x}
    (hU : IsSmoothVectorField U) (hW : IsSmoothVectorField W)
    (hF2 : ∀ (V : Π x : M₁, TangentSpace I₁ x) (Y : Π x : M₂, TangentSpace I₂ x),
      IsSmoothVectorField V → IsSmoothVectorField Y →
      lieDerivativeVectorField (I₁.prod I₂) (liftFst I₂ V) (liftSnd I₁ Y) = 0)
    (hF2' : ∀ (Y : Π x : M₂, TangentSpace I₂ x) (V : Π x : M₁, TangentSpace I₁ x),
      IsSmoothVectorField Y → IsSmoothVectorField V →
      lieDerivativeVectorField (I₁.prod I₂) (liftSnd I₁ Y) (liftFst I₂ V) = 0)
    (hF3 : ∀ (V U' : Π x : M₁, TangentSpace I₁ x),
      IsSmoothVectorField V → IsSmoothVectorField U' →
      lieDerivativeVectorField (I₁.prod I₂) (liftFst I₂ V) (liftFst I₂ U')
        = liftFst (M₂ := M₂) I₂ (lieDerivativeVectorField I₁ V U'))
    (hF3' : ∀ (Y Y' : Π x : M₂, TangentSpace I₂ x),
      IsSmoothVectorField Y → IsSmoothVectorField Y' →
      lieDerivativeVectorField (I₁.prod I₂) (liftSnd I₁ Y) (liftSnd I₁ Y')
        = liftSnd (M₁ := M₁) I₁ (lieDerivativeVectorField I₂ Y Y'))
    (p : M₁ × M₂) :
    ((productMetric g₁ g₂).leviCivita).cov p (liftFst I₂ U p) (liftSnd I₁ W) = 0 := by
  have hUl : IsSmoothVectorField (liftFst (M₂ := M₂) I₂ U) := isSmoothVectorField_liftFst hU
  have hWl : IsSmoothVectorField (liftSnd (M₁ := M₁) I₁ W) := isSmoothVectorField_liftSnd hW
  -- Test against a first-factor lift `liftFst Z₀`.
  have key₁ : ∀ (Z₀ : Π x : M₁, TangentSpace I₁ x), IsSmoothVectorField Z₀ →
      (productMetric g₁ g₂).metricInner p
        (((productMetric g₁ g₂).leviCivita).cov p (liftFst I₂ U p) (liftSnd I₁ W))
        (liftFst I₂ Z₀ p) = 0 := by
    intro Z₀ hZ₀
    have hZl : IsSmoothVectorField (liftFst (M₂ := M₂) I₂ Z₀) := isSmoothVectorField_liftFst hZ₀
    have hk := ((productMetric g₁ g₂).leviCivita).koszul hWl hUl hZl p
    have hzero :
        koszulExpression (productMetric g₁ g₂) (liftSnd I₁ W) (liftFst I₂ U) (liftFst I₂ Z₀) p
          = 0 := by
      unfold koszulExpression
      rw [productMetric_liftFst_liftFst_eq_comp g₁ g₂ U Z₀,
        productMetric_liftSnd_liftFst_eq_zero g₁ g₂ W Z₀,
        productMetric_liftSnd_liftFst_eq_zero g₁ g₂ W U,
        hF2' W U hW hU, hF2 Z₀ W hZ₀ hW, hF3 U Z₀ hU hZ₀]
      rw [directionalDerivative_liftSnd_comp_fst
          (mdifferentiable_metricInner_of_smooth hU hZ₀),
        directionalDerivative_const, directionalDerivative_const,
        productMetric_liftFst_liftSnd g₁ g₂ (lieDerivativeVectorField I₁ U Z₀) W p]
      simp
    rw [hzero] at hk
    linarith [hk]
  -- Test against a second-factor lift `liftSnd Z₀`.
  have key₂ : ∀ (Z₀ : Π x : M₂, TangentSpace I₂ x), IsSmoothVectorField Z₀ →
      (productMetric g₁ g₂).metricInner p
        (((productMetric g₁ g₂).leviCivita).cov p (liftFst I₂ U p) (liftSnd I₁ W))
        (liftSnd I₁ Z₀ p) = 0 := by
    intro Z₀ hZ₀
    have hZl : IsSmoothVectorField (liftSnd (M₁ := M₁) I₁ Z₀) := isSmoothVectorField_liftSnd hZ₀
    have hk := ((productMetric g₁ g₂).leviCivita).koszul hWl hUl hZl p
    have hzero :
        koszulExpression (productMetric g₁ g₂) (liftSnd I₁ W) (liftFst I₂ U) (liftSnd I₁ Z₀) p
          = 0 := by
      unfold koszulExpression
      rw [productMetric_liftFst_liftSnd_eq_zero g₁ g₂ U Z₀,
        productMetric_liftSnd_liftSnd_eq_comp g₁ g₂ W Z₀,
        productMetric_liftSnd_liftFst_eq_zero g₁ g₂ W U,
        hF2' W U hW hU, hF2 U Z₀ hU hZ₀, hF3' Z₀ W hZ₀ hW]
      rw [directionalDerivative_liftFst_comp_snd
          (mdifferentiable_metricInner_of_smooth hW hZ₀),
        directionalDerivative_const, directionalDerivative_const,
        productMetric_liftSnd_liftFst g₁ g₂ (lieDerivativeVectorField I₂ Z₀ W) U p]
      simp
    rw [hzero] at hk
    linarith [hk]
  -- Nondegeneracy: every `(z₁,0)` / `(0,z₂)` is the value at `p` of a smooth lift.
  refine eq_zero_of_metricInner_prod_split g₁ g₂ p _ (fun z₁ => ?_) (fun z₂ => ?_)
  · have h := key₁ (extendTangentVector p.1 z₁) (extendTangentVector p.1 z₁).smooth
    simpa [liftFst_apply, extendTangentVector_apply] using h
  · have h := key₂ (extendTangentVector p.2 z₂) (extendTangentVector p.2 z₂).smooth
    simpa [liftSnd_apply, extendTangentVector_apply] using h

/-! ## Lemma A, unconditionally

`cov_liftFst_liftSnd_eq_zero_of_brackets` takes the four bracket facts as
hypotheses; all four are now theorems, so we discharge them once and for all. -/

/-- **Lemma A.** `∇_{liftFst U}(liftSnd W) = 0` for the Levi-Civita connection of a
product metric: the two factors of a Riemannian product are totally geodesic against
each other. -/
theorem cov_liftFst_liftSnd (g₁ : RiemannianMetric I₁ M₁) (g₂ : RiemannianMetric I₂ M₂)
    {U : Π x : M₁, TangentSpace I₁ x} {W : Π x : M₂, TangentSpace I₂ x}
    (hU : IsSmoothVectorField U) (hW : IsSmoothVectorField W) (p : M₁ × M₂) :
    ((productMetric g₁ g₂).leviCivita).cov p (liftFst I₂ U p) (liftSnd I₁ W) = 0 :=
  cov_liftFst_liftSnd_eq_zero_of_brackets g₁ g₂ hU hW
    (fun _ _ hV hY => lieDerivativeVectorField_liftFst_liftSnd hV hY)
    (fun _ _ hY hV => lieDerivativeVectorField_liftSnd_liftFst hY hV)
    (fun _ _ hV hU' => lieDerivativeVectorField_liftFst_liftFst hV hU')
    (fun _ _ hY hY' => lieDerivativeVectorField_liftSnd_liftSnd hY hY')
    p

/-! ## The mirror of Lemma A -/

/-- **Mirror of Lemma A.** `∇_{liftSnd W}(liftFst Z) = 0`.

Torsion-freeness turns this into Lemma A: `∇_{liftFst Z}(liftSnd W) − ∇_{liftSnd W}(liftFst Z)`
is the bracket `[liftFst Z, liftSnd W]`, which vanishes by **F2**, and the first summand
vanishes by Lemma A. -/
theorem cov_liftSnd_liftFst (g₁ : RiemannianMetric I₁ M₁) (g₂ : RiemannianMetric I₂ M₂)
    {W : Π x : M₂, TangentSpace I₂ x} {Z : Π x : M₁, TangentSpace I₁ x}
    (hW : IsSmoothVectorField W) (hZ : IsSmoothVectorField Z) (p : M₁ × M₂) :
    ((productMetric g₁ g₂).leviCivita).cov p (liftSnd I₁ W p) (liftFst I₂ Z) = 0 := by
  have ht := ((productMetric g₁ g₂).leviCivita).torsion_free
    (isSmoothVectorField_liftFst (M₂ := M₂) hZ)
    (isSmoothVectorField_liftSnd (M₁ := M₁) hW) p
  rw [lieDerivativeVectorField_liftFst_liftSnd hZ hW,
    cov_liftFst_liftSnd g₁ g₂ hZ hW p] at ht
  rw [show ((0 : Π x : M₁ × M₂, TangentSpace (I₁.prod I₂) x) p) = 0 from rfl, zero_sub,
    neg_eq_zero] at ht
  exact ht

/-! ## The splitting lemma -/


/-- **Koszul splits along `π₁`.** The Koszul expression of three first-factor lifts is the
pullback along `π₁` of the Koszul expression of the corresponding fields on `M₁`.

Each of the six terms matches: the three directional derivatives by **G2**
(`directionalDerivative_liftFst_comp_fst`) applied to the `π₁`-pullback shape
supplied by `productMetric_liftFst_liftFst_eq_comp`, and the three bracket terms by
**F3** (`lieDerivativeVectorField_liftFst_liftFst`) followed by **G1**. -/
theorem koszulExpression_liftFst (V U : Π x : M₁, TangentSpace I₁ x)
    (hV : IsSmoothVectorField V) (hU : IsSmoothVectorField U)
    (Z₀ : Π x : M₁, TangentSpace I₁ x) (hZ₀ : IsSmoothVectorField Z₀) (p : M₁ × M₂) :
    koszulExpression (productMetric g₁ g₂) (liftFst I₂ V) (liftFst I₂ U) (liftFst I₂ Z₀) p
      = koszulExpression g₁ V U Z₀ p.1 := by
  unfold koszulExpression
  rw [productMetric_liftFst_liftFst_eq_comp g₁ g₂ U Z₀,
    productMetric_liftFst_liftFst_eq_comp g₁ g₂ V Z₀,
    productMetric_liftFst_liftFst_eq_comp g₁ g₂ V U,
    lieDerivativeVectorField_liftFst_liftFst hV hU,
    lieDerivativeVectorField_liftFst_liftFst hU hZ₀,
    lieDerivativeVectorField_liftFst_liftFst hZ₀ hV]
  rw [directionalDerivative_liftFst_comp_fst (mdifferentiable_metricInner_of_smooth hU hZ₀),
    directionalDerivative_liftFst_comp_fst (mdifferentiable_metricInner_of_smooth hV hZ₀),
    directionalDerivative_liftFst_comp_fst (mdifferentiable_metricInner_of_smooth hV hU),
    productMetric_liftFst_liftFst g₁ g₂ (lieDerivativeVectorField I₁ V U) Z₀ p,
    productMetric_liftFst_liftFst g₁ g₂ (lieDerivativeVectorField I₁ U Z₀) V p,
    productMetric_liftFst_liftFst g₁ g₂ (lieDerivativeVectorField I₁ Z₀ V) U p]

/-- **The splitting lemma.** The Levi-Civita connection of a product metric restricted to
first-factor lifts is the lift of the Levi-Civita connection of `g₁`:
`∇^{M₁×M₂}_{liftFst U}(liftFst V) = liftFst (∇^{M₁}_U V)`.

Proof: let `w = ∇_{liftFst U}(liftFst V)`. Koszul tested against a *second*-factor lift
`liftSnd Z₀` kills all six terms (`koszulExpression_liftFst`'s sibling computation
`key₂` below), so `w` is orthogonal to every `(0, z₂)`. Koszul tested against a
*first*-factor lift `liftFst Z₀` is, by `koszulExpression_liftFst`, exactly the `M₁`
Koszul expression, hence pairs like `∇^{M₁}_U V` against every `(z₁, 0)`. Nondegeneracy
(`eq_zero_of_metricInner_prod_split`) applied to the difference finishes. -/
theorem cov_liftFst_liftFst
    {U V : Π x : M₁, TangentSpace I₁ x} (hU : IsSmoothVectorField U)
    (hV : IsSmoothVectorField V) (p : M₁ × M₂) :
    ((productMetric g₁ g₂).leviCivita).cov p (liftFst I₂ U p) (liftFst I₂ V)
      = liftFst (M₂ := M₂) I₂ ((g₁.leviCivita).covField U V) p := by
  have hUl : IsSmoothVectorField (liftFst (M₂ := M₂) I₂ U) := isSmoothVectorField_liftFst hU
  have hVl : IsSmoothVectorField (liftFst (M₂ := M₂) I₂ V) := isSmoothVectorField_liftFst hV
  -- Tested against a first-factor lift, `w` pairs exactly like `∇^{M₁}_U V`.
  have key₁ : ∀ (Z₀ : Π x : M₁, TangentSpace I₁ x), IsSmoothVectorField Z₀ →
      (productMetric g₁ g₂).metricInner p
        (((productMetric g₁ g₂).leviCivita).cov p (liftFst I₂ U p) (liftFst I₂ V))
        (liftFst I₂ Z₀ p)
        = g₁.metricInner p.1 ((g₁.leviCivita).cov p.1 (U p.1) V) (Z₀ p.1) := by
    intro Z₀ hZ₀
    have hZl : IsSmoothVectorField (liftFst (M₂ := M₂) I₂ Z₀) := isSmoothVectorField_liftFst hZ₀
    have hk := ((productMetric g₁ g₂).leviCivita).koszul hVl hUl hZl p
    have hk1 := (g₁.leviCivita).koszul hV hU hZ₀ p.1
    rw [koszulExpression_liftFst g₁ g₂ V U hV hU Z₀ hZ₀ p, ← hk1] at hk
    linarith [hk]
  -- Tested against a second-factor lift, every Koszul term dies.
  have key₂ : ∀ (Z₀ : Π x : M₂, TangentSpace I₂ x), IsSmoothVectorField Z₀ →
      (productMetric g₁ g₂).metricInner p
        (((productMetric g₁ g₂).leviCivita).cov p (liftFst I₂ U p) (liftFst I₂ V))
        (liftSnd I₁ Z₀ p) = 0 := by
    intro Z₀ hZ₀
    have hZl : IsSmoothVectorField (liftSnd (M₁ := M₁) I₁ Z₀) := isSmoothVectorField_liftSnd hZ₀
    have hk := ((productMetric g₁ g₂).leviCivita).koszul hVl hUl hZl p
    have hzero : koszulExpression (productMetric g₁ g₂) (liftFst I₂ V) (liftFst I₂ U)
        (liftSnd I₁ Z₀) p = 0 := by
      unfold koszulExpression
      rw [productMetric_liftFst_liftSnd_eq_zero g₁ g₂ U Z₀,
        productMetric_liftFst_liftSnd_eq_zero g₁ g₂ V Z₀,
        productMetric_liftFst_liftFst_eq_comp g₁ g₂ V U,
        lieDerivativeVectorField_liftFst_liftFst hV hU,
        lieDerivativeVectorField_liftFst_liftSnd hU hZ₀,
        lieDerivativeVectorField_liftSnd_liftFst hZ₀ hV]
      rw [directionalDerivative_liftSnd_comp_fst (mdifferentiable_metricInner_of_smooth hV hU),
        directionalDerivative_const, directionalDerivative_const,
        productMetric_liftFst_liftSnd g₁ g₂ (lieDerivativeVectorField I₁ V U) Z₀ p]
      simp
    rw [hzero] at hk
    linarith [hk]
  -- Nondegeneracy on the difference.
  have hsub : ((productMetric g₁ g₂).leviCivita).cov p (liftFst I₂ U p) (liftFst I₂ V)
      - liftFst (M₂ := M₂) I₂ ((g₁.leviCivita).covField U V) p = 0 := by
    refine eq_zero_of_metricInner_prod_split g₁ g₂ p _ (fun z₁ => ?_) (fun z₂ => ?_)
    · have h₁ := key₁ (extendTangentVector p.1 z₁) (extendTangentVector p.1 z₁).smooth
      have h₂ := productMetric_liftFst_liftFst g₁ g₂ ((g₁.leviCivita).covField U V)
        (⇑(extendTangentVector p.1 z₁)) p
      rw [(productMetric g₁ g₂).metricInner_sub_left]
      have e : ((z₁, (0 : TangentSpace I₂ p.2)) : TangentSpace (I₁.prod I₂) p)
          = liftFst I₂ (⇑(extendTangentVector p.1 z₁)) p := by
        rw [liftFst_apply, extendTangentVector_apply]
      rw [e, h₁, h₂, AffineConnection.covField_apply, extendTangentVector_apply, sub_self]
    · have h₁ := key₂ (extendTangentVector p.2 z₂) (extendTangentVector p.2 z₂).smooth
      have h₂ := productMetric_liftFst_liftSnd g₁ g₂ ((g₁.leviCivita).covField U V)
        (⇑(extendTangentVector p.2 z₂)) p
      rw [(productMetric g₁ g₂).metricInner_sub_left]
      have e : (((0 : TangentSpace I₁ p.1), z₂) : TangentSpace (I₁.prod I₂) p)
          = liftSnd I₁ (⇑(extendTangentVector p.2 z₂)) p := by
        rw [liftSnd_apply, extendTangentVector_apply]
      rw [e, h₁, h₂, sub_zero]
  exact sub_eq_zero.mp hsub

/-! ## Petersen, Exercise 3.4.9

The pointwise curvature tensor's evaluation lemma `curvatureTensorAt_apply` rests on the
locality of the connection, so — exactly as in `Ch03/SectionalCurvature.lean`, whose
variable block already carries `[LocallyCompactSpace M]` — the two factors are assumed
locally compact; `Prod.locallyCompactSpace` then supplies `LocallyCompactSpace (M₁ × M₂)`. -/

variable [LocallyCompactSpace M₁] [LocallyCompactSpace M₂]

/-- **Petersen, Exercise 3.4.9.** On a Riemannian product `(M₁ × M₂, g₁ + g₂)`, a vector
field `X` on `M₁` and a vector field `Y` on `M₂`, regarded on the product, satisfy
`∇_X Y = 0`; consequently every `X`–`Y` plane is flat, `sec(X, Y) = 0`.

The `sec` half: `R(liftSnd Y, liftFst X)(liftFst X)` has all three terms zero — the
bracket `[liftSnd Y, liftFst X]` vanishes (**F2'**), `∇_{liftSnd Y}(liftFst X)` vanishes
as a *field* (`cov_liftSnd_liftFst`), and `∇_{liftFst X}(liftFst X) = liftFst(∇^{M₁}_X X)`
splits (`cov_liftFst_liftFst`), which `cov_liftSnd_liftFst` then annihilates. -/
theorem exercise3_4_9
    {X : Π x : M₁, TangentSpace I₁ x} {Y : Π x : M₂, TangentSpace I₂ x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y) (p : M₁ × M₂) :
    ((productMetric g₁ g₂).leviCivita).cov p (liftFst I₂ X p) (liftSnd I₁ Y) = 0
      ∧ sectionalCurvature ((productMetric g₁ g₂).leviCivita) p
          (liftFst I₂ X p) (liftSnd I₁ Y p) = 0 := by
  refine ⟨cov_liftFst_liftSnd g₁ g₂ hX hY p, ?_⟩
  have hXl : IsSmoothVectorField (liftFst (M₂ := M₂) I₂ X) := isSmoothVectorField_liftFst hX
  have hYl : IsSmoothVectorField (liftSnd (M₁ := M₁) I₁ Y) := isSmoothVectorField_liftSnd hY
  -- `∇_{liftFst X}(liftFst X)` splits as a field.
  have hcovXX : ((productMetric g₁ g₂).leviCivita).toAffineConnection.covField
      (liftFst I₂ X) (liftFst I₂ X)
      = liftFst (M₂ := M₂) I₂ ((g₁.leviCivita).covField X X) :=
    funext fun q => cov_liftFst_liftFst g₁ g₂ hX hX q
  -- `∇_{liftSnd Y}(liftFst X)` is the zero field.
  have hcovYX : ((productMetric g₁ g₂).leviCivita).toAffineConnection.covField
      (liftSnd I₁ Y) (liftFst I₂ X)
      = fun q : M₁ × M₂ => (0 : TangentSpace (I₁.prod I₂) q) :=
    funext fun q => cov_liftSnd_liftFst g₁ g₂ hY hX q
  have hnum : curvatureTensor ((productMetric g₁ g₂).leviCivita).toAffineConnection
      (liftSnd I₁ Y) (liftFst I₂ X) (liftFst I₂ X) p = 0 := by
    rw [curvatureTensor_apply, hcovXX, hcovYX,
      lieDerivativeVectorField_liftSnd_liftFst hY hX,
      cov_liftSnd_liftFst g₁ g₂ (Z := (g₁.leviCivita).covField X X) hY
        ((g₁.leviCivita).smooth_cov hX hX) p,
      AffineConnection.cov_zero_field,
      show ((0 : Π x : M₁ × M₂, TangentSpace (I₁.prod I₂) x) p) = 0 from rfl,
      AffineConnection.cov_zero_direction, sub_zero, sub_zero]
  unfold sectionalCurvature directionalCurvatureOperator
  rw [curvatureTensorAt_apply _ hYl hXl hXl p, hnum,
    RiemannianMetric.metricInner_zero_left, zero_div]

end PetersenLib
