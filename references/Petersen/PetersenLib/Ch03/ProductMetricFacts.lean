import PetersenLib.Ch03.ProductCurvature

/-!
# Product metric vs. lifted vector fields

Elementary facts relating `productMetric g₁ g₂` to the lifts `liftFst`/`liftSnd`
of vector fields from the factors of `M₁ × M₂`:

* **F1** the cross inner product `⟨liftFst V, liftSnd W⟩` vanishes identically;
* **G1** `⟨liftFst V, liftFst U⟩ = ⟨V, U⟩_{g₁} ∘ π₁`, and its `liftSnd`/`π₂` mirror.

Each is stated twice: pointwise, and as an equality of *functions* on `M₁ × M₂`.
The function-level versions are the ones the Koszul computation needs, since they
expose the pullback shape `· ∘ Prod.fst` / `· ∘ Prod.snd` that the lemmas
`directionalDerivative_liftFst_comp_fst` etc. match against.
-/

open Bundle Set Function
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

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

/-! ## Pointwise statements -/

/-- **Math (F1).** The two factors of a product metric are orthogonal: a
first-factor lift `(V p₁, 0)` and a second-factor lift `(0, W p₂)` pair to
`⟨V p₁, 0⟩_{g₁} + ⟨0, W p₂⟩_{g₂} = 0`. -/
@[simp]
theorem productMetric_liftFst_liftSnd (V : Π x : M₁, TangentSpace I₁ x)
    (W : Π x : M₂, TangentSpace I₂ x) (x : M₁ × M₂) :
    (productMetric g₁ g₂).metricInner x (liftFst I₂ V x) (liftSnd I₁ W x) = 0 := by
  simp only [liftFst_apply, liftSnd_apply, productMetric_apply,
    RiemannianMetric.metricInner_zero_left, RiemannianMetric.metricInner_zero_right, add_zero]

/-- **Math (F1').** The `liftSnd`/`liftFst` order of `productMetric_liftFst_liftSnd`. -/
@[simp]
theorem productMetric_liftSnd_liftFst (W : Π x : M₂, TangentSpace I₂ x)
    (V : Π x : M₁, TangentSpace I₁ x) (x : M₁ × M₂) :
    (productMetric g₁ g₂).metricInner x (liftSnd I₁ W x) (liftFst I₂ V x) = 0 := by
  simp only [liftFst_apply, liftSnd_apply, productMetric_apply,
    RiemannianMetric.metricInner_zero_left, RiemannianMetric.metricInner_zero_right, add_zero]

/-- **Math (G1).** On two first-factor lifts the product metric is just `g₁`,
evaluated at the first component: the second-factor contribution `⟨0, 0⟩_{g₂}`
drops out. -/
@[simp]
theorem productMetric_liftFst_liftFst (V U : Π x : M₁, TangentSpace I₁ x) (x : M₁ × M₂) :
    (productMetric g₁ g₂).metricInner x (liftFst I₂ V x) (liftFst I₂ U x)
      = g₁.metricInner x.1 (V x.1) (U x.1) := by
  simp only [liftFst_apply, productMetric_apply,
    RiemannianMetric.metricInner_zero_left, add_zero]

/-- **Math (G1').** The second-factor mirror of `productMetric_liftFst_liftFst`. -/
@[simp]
theorem productMetric_liftSnd_liftSnd (W Z : Π x : M₂, TangentSpace I₂ x) (x : M₁ × M₂) :
    (productMetric g₁ g₂).metricInner x (liftSnd I₁ W x) (liftSnd I₁ Z x)
      = g₂.metricInner x.2 (W x.2) (Z x.2) := by
  simp only [liftSnd_apply, productMetric_apply,
    RiemannianMetric.metricInner_zero_left, zero_add]

/-! ## Function-level restatements

These are the forms consumed by the Koszul computation: the right-hand sides are
literally pullbacks along `Prod.fst` / `Prod.snd`, resp. the constant `0`, so the
directional-derivative lemmas for lifts apply to them directly. -/

/-- **Math.** `⟨liftFst V, liftFst U⟩` is the pullback along `π₁` of the function
`p₁ ↦ ⟨V p₁, U p₁⟩_{g₁}` on `M₁`. -/
theorem productMetric_liftFst_liftFst_eq_comp (V U : Π x : M₁, TangentSpace I₁ x) :
    (fun q : M₁ × M₂ => (productMetric g₁ g₂).metricInner q (liftFst I₂ V q) (liftFst I₂ U q))
      = (fun p₁ : M₁ => g₁.metricInner p₁ (V p₁) (U p₁)) ∘ Prod.fst :=
  funext fun q => productMetric_liftFst_liftFst g₁ g₂ V U q

/-- **Math.** `⟨liftSnd W, liftSnd Z⟩` is the pullback along `π₂` of the function
`p₂ ↦ ⟨W p₂, Z p₂⟩_{g₂}` on `M₂`. -/
theorem productMetric_liftSnd_liftSnd_eq_comp (W Z : Π x : M₂, TangentSpace I₂ x) :
    (fun q : M₁ × M₂ => (productMetric g₁ g₂).metricInner q (liftSnd I₁ W q) (liftSnd I₁ Z q))
      = (fun p₂ : M₂ => g₂.metricInner p₂ (W p₂) (Z p₂)) ∘ Prod.snd :=
  funext fun q => productMetric_liftSnd_liftSnd g₁ g₂ W Z q

/-- **Math.** The cross inner product `⟨liftFst V, liftSnd W⟩` is the zero function. -/
theorem productMetric_liftFst_liftSnd_eq_zero (V : Π x : M₁, TangentSpace I₁ x)
    (W : Π x : M₂, TangentSpace I₂ x) :
    (fun q : M₁ × M₂ => (productMetric g₁ g₂).metricInner q (liftFst I₂ V q) (liftSnd I₁ W q))
      = fun _ : M₁ × M₂ => (0 : ℝ) :=
  funext fun q => productMetric_liftFst_liftSnd g₁ g₂ V W q

/-- **Math.** The cross inner product `⟨liftSnd W, liftFst V⟩` is the zero function. -/
theorem productMetric_liftSnd_liftFst_eq_zero (W : Π x : M₂, TangentSpace I₂ x)
    (V : Π x : M₁, TangentSpace I₁ x) :
    (fun q : M₁ × M₂ => (productMetric g₁ g₂).metricInner q (liftSnd I₁ W q) (liftFst I₂ V q))
      = fun _ : M₁ × M₂ => (0 : ℝ) :=
  funext fun q => productMetric_liftSnd_liftFst g₁ g₂ W V q

/-- **Nondegeneracy against the two lift directions.** A tangent vector of `M₁ × M₂` that is
`productMetric`-orthogonal to every purely-first-factor vector `(z₁, 0)` and every
purely-second-factor vector `(0, z₂)` vanishes.

This is the step that converts the Koszul computation — which only ever tests against *lifted*
fields — into an honest vanishing statement. -/
theorem eq_zero_of_metricInner_prod_split
    (g₁ : RiemannianMetric I₁ M₁) (g₂ : RiemannianMetric I₂ M₂)
    (p : M₁ × M₂) (w : TangentSpace (I₁.prod I₂) p)
    (h₁ : ∀ z₁ : TangentSpace I₁ p.1,
      (productMetric g₁ g₂).metricInner p w
        ((z₁, (0 : TangentSpace I₂ p.2)) : TangentSpace (I₁.prod I₂) p) = 0)
    (h₂ : ∀ z₂ : TangentSpace I₂ p.2,
      (productMetric g₁ g₂).metricInner p w
        (((0 : TangentSpace I₁ p.1), z₂) : TangentSpace (I₁.prod I₂) p) = 0) :
    w = 0 := by
  -- Testing against `(w.1, 0)` isolates the first factor: `g₁(w.1, w.1) = 0`, so `w.1 = 0`.
  have hw1 : w.1 = 0 := by
    by_contra h
    have hz := h₁ w.1
    rw [productMetric_apply] at hz
    simp only [g₂.metricInner_zero_right, add_zero] at hz
    exact absurd hz (g₁.metricInner_self_pos p.1 w.1 h).ne'
  -- Symmetrically for the second factor.
  have hw2 : w.2 = 0 := by
    by_contra h
    have hz := h₂ w.2
    rw [productMetric_apply] at hz
    simp only [g₁.metricInner_zero_right, zero_add] at hz
    exact absurd hz (g₂.metricInner_self_pos p.2 w.2 h).ne'
  exact Prod.ext hw1 hw2

end PetersenLib
