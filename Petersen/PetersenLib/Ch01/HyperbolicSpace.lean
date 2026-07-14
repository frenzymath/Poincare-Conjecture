import PetersenLib.Ch01.Minkowski
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Petersen Ch. 1, Example 1.1.7 — hyperbolic space

The **hyperbolic space** `H^n(R) ⊂ ℝ^{n,1}` is the branch with `x^{n+1} > 0`
of the hyperboloid `(x¹)² + ⋯ + (xⁿ)² - (x^{n+1})² = -R²`, with the metric
induced from the Minkowski metric on `ℝ^{n,1}`. The induced form is positive
definite (by the Cauchy–Schwarz computation of Petersen's text), hence a
genuine Riemannian metric on `H^n(R)`.

Formalized with `ℝ^{n,1} := EuclideanSpace ℝ (Fin n) × ℝ`:

* `hyperboloid n R`: the upper branch, as a subtype;
* the manifold structure via the single global chart `(x, t) ↦ x`
  (`hyperboloidChart`, `PartialHomeomorph.singletonChartedSpace`);
* `hyperboloidInclusion`: the smooth inclusion `H^n(R) ↪ ℝ^{n,1}`, with its
  differential computed explicitly (`mfderiv_hyperboloidInclusion`:
  `u ↦ (u, ⟪p₁, u⟫ / p_t)`) and shown injective;
* `hyperbolicSpace n R`: the induced Riemannian metric, whose positivity is
  the displayed Cauchy–Schwarz estimate
  `|v|² ≥ (R / p^{n+1})² ∑ (vⁱ)² > 0` (`minkowskiForm_inclusionDeriv_pos`).

The positivity hypothesis `0 < R` is carried as a `Fact` instance so that the
charted-space and manifold instances on `hyperboloid n R` can pick it up.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Example 1.1.7.
-/

open Bundle Bornology
open scoped ContDiff Manifold Topology RealInnerProductSpace

noncomputable section

namespace PetersenLib

/-! ## The hyperboloid -/

/-- **Math.** Petersen Example 1.1.7: the upper branch (`x^{n+1} > 0`) of the
hyperboloid `(x¹)² + ⋯ + (xⁿ)² - (x^{n+1})² = -R²` in
`ℝ^{n,1} = EuclideanSpace ℝ (Fin n) × ℝ`; as a set, the underlying carrier of
hyperbolic space `H^n(R)`. -/
def hyperboloid (n : ℕ) (R : ℝ) : Type :=
  { x : EuclideanSpace ℝ (Fin n) × ℝ // ‖x.1‖ ^ 2 - x.2 ^ 2 = -R ^ 2 ∧ 0 < x.2 }
deriving TopologicalSpace

variable {n : ℕ} {R : ℝ}

/-- **Math.** Points of the hyperboloid have positive last coordinate. -/
theorem hyperboloid_t_pos (p : hyperboloid n R) : 0 < p.1.2 :=
  p.2.2

/-- **Math.** The defining equation, rearranged: `‖p₁‖² + R² = p_t²`. -/
theorem hyperboloid_norm_sq_add (p : hyperboloid n R) :
    ‖p.1.1‖ ^ 2 + R ^ 2 = p.1.2 ^ 2 := by
  have h := p.2.1
  linarith

/-- **Math.** On the hyperboloid, `√(‖p₁‖² + R²) = p_t` (the positive root). -/
theorem hyperboloid_sqrt_eq (p : hyperboloid n R) :
    Real.sqrt (‖p.1.1‖ ^ 2 + R ^ 2) = p.1.2 := by
  rw [hyperboloid_norm_sq_add p, Real.sqrt_sq (hyperboloid_t_pos p).le]

/-! ## The global parametrization `x ↦ (x, √(‖x‖² + R²))` -/

/-- **Math.** The global parametrization of the upper hyperboloid branch
inside the ambient space: `x ↦ (x, √(‖x‖² + R²))`. Its image is `H^n(R)` for
`R > 0`, and it inverts the coordinate projection `(x, t) ↦ x`. -/
def hyperboloidLift (n : ℕ) (R : ℝ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) × ℝ :=
  fun x => (x, Real.sqrt (‖x‖ ^ 2 + R ^ 2))

/-- **Math.** For `R > 0` the parametrization `x ↦ (x, √(‖x‖² + R²))` is `C^∞`:
the radicand is everywhere positive, and `√` is smooth away from `0`. -/
theorem contDiff_hyperboloidLift (n : ℕ) (R : ℝ) [Fact (0 < R)] :
    ContDiff ℝ ∞ (hyperboloidLift n R) := by
  have hR : 0 < R := Fact.out
  refine contDiff_id.prodMk ?_
  rw [contDiff_iff_contDiffAt]
  intro x
  have h0 : (0 : ℝ) < ‖x‖ ^ 2 + R ^ 2 := by
    have h1 : (0 : ℝ) ≤ ‖x‖ ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) < R ^ 2 := pow_pos hR 2
    linarith
  exact (Real.contDiffAt_sqrt h0.ne').comp x
    (((contDiff_norm_sq ℝ).add contDiff_const).contDiffAt)

/-- **Math.** Derivative of the parametrization at `a`:
`u ↦ (u, ⟪a, u⟫ / √(‖a‖² + R²))`, obtained from the derivative `2⟪a, ·⟫` of
`‖·‖²` and the chain rule for `√`. -/
theorem hyperboloidLift_hasFDerivAt (n : ℕ) (R : ℝ) (a : EuclideanSpace ℝ (Fin n))
    (h : ‖a‖ ^ 2 + R ^ 2 ≠ 0) :
    HasFDerivAt (hyperboloidLift n R)
      ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).prod
        ((Real.sqrt (‖a‖ ^ 2 + R ^ 2))⁻¹ • innerSL ℝ a)) a := by
  have h1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2 + R ^ 2)
      (2 • innerSL ℝ a) a :=
    (hasStrictFDerivAt_norm_sq a).hasFDerivAt.add_const (R ^ 2)
  have h2 := h1.sqrt h
  have h3 : (1 / (2 * Real.sqrt (‖a‖ ^ 2 + R ^ 2))) • (2 • innerSL ℝ a)
      = (Real.sqrt (‖a‖ ^ 2 + R ^ 2))⁻¹ • innerSL ℝ a := by
    ext u
    simp only [ContinuousLinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul]
    rw [one_div, mul_inv]
    ring
  rw [h3] at h2
  exact HasFDerivAt.prodMk (hasFDerivAt_id a) h2

/-! ## Manifold structure via a single global chart -/

/-- **Math.** The single global chart of `H^n(R)`: the coordinate projection
`(x, t) ↦ x`, a homeomorphism of the upper hyperboloid branch onto
`EuclideanSpace ℝ (Fin n)` with inverse `x ↦ (x, √(‖x‖² + R²))` (for `R > 0`). -/
def hyperboloidChart (n : ℕ) (R : ℝ) [Fact (0 < R)] :
    OpenPartialHomeomorph (hyperboloid n R) (EuclideanSpace ℝ (Fin n)) where
  toFun p := p.1.1
  invFun x := ⟨(x, Real.sqrt (‖x‖ ^ 2 + R ^ 2)), by
    have hR : 0 < R := Fact.out
    have h0 : (0 : ℝ) < ‖x‖ ^ 2 + R ^ 2 := by
      have h1 : (0 : ℝ) ≤ ‖x‖ ^ 2 := sq_nonneg _
      have h2 : (0 : ℝ) < R ^ 2 := pow_pos hR 2
      linarith
    constructor
    · rw [Real.sq_sqrt h0.le]
      ring
    · exact Real.sqrt_pos.mpr h0⟩
  source := Set.univ
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' _ _ := Set.mem_univ _
  left_inv' p _ := Subtype.ext (Prod.ext rfl (hyperboloid_sqrt_eq p))
  right_inv' _ _ := rfl
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := (continuous_fst.comp continuous_subtype_val).continuousOn
  continuousOn_invFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    exact continuous_id.prodMk
      (Real.continuous_sqrt.comp ((continuous_norm.pow 2).add continuous_const))

/-- **Eng.** The charted-space structure on the hyperboloid induced by the
single global chart `(x, t) ↦ x`. -/
instance {n : ℕ} {R : ℝ} [Fact (0 < R)] :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (hyperboloid n R) :=
  (hyperboloidChart n R).singletonChartedSpace rfl

/-- **Math.** With a single global chart, the change of charts is the
identity, so the hyperboloid is a `C^∞` manifold. -/
instance {n : ℕ} {R : ℝ} [Fact (0 < R)] :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (hyperboloid n R) :=
  (hyperboloidChart n R).isManifold_singleton rfl

instance {n : ℕ} {R : ℝ} [Fact (0 < R)] : Nonempty (hyperboloid n R) :=
  ⟨⟨((0 : EuclideanSpace ℝ (Fin n)), R), by
    constructor
    · show ‖(0 : EuclideanSpace ℝ (Fin n))‖ ^ 2 - R ^ 2 = -R ^ 2
      rw [norm_zero]
      ring
    · exact Fact.out⟩⟩

/-! ## The inclusion `H^n(R) ↪ ℝ^{n,1}` -/

/-- **Math.** The inclusion `ι : H^n(R) → ℝ^{n,1}` of the hyperboloid branch
into the ambient Minkowski space. -/
def hyperboloidInclusion (n : ℕ) (R : ℝ) :
    hyperboloid n R → EuclideanSpace ℝ (Fin n) × ℝ :=
  Subtype.val

/-- **Math.** The global chart `(x, t) ↦ x`, read as a map of manifolds, is
`C^∞` (it *is* the chart). -/
theorem contMDiff_hyperboloid_proj (n : ℕ) (R : ℝ) [Fact (0 < R)] :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun p : hyperboloid n R => p.1.1) := by
  have h : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (chartAt (EuclideanSpace ℝ (Fin n)) (Classical.arbitrary (hyperboloid n R)))
      (chartAt (EuclideanSpace ℝ (Fin n)) (Classical.arbitrary (hyperboloid n R))).source :=
    contMDiffOn_chart
  exact contMDiffOn_univ.mp h

/-- **Math.** The inclusion `ι : H^n(R) → ℝ^{n,1}` is `C^∞`: in the global
chart it reads as the parametrization `x ↦ (x, √(‖x‖² + R²))`, which is smooth
since `‖x‖² + R² > 0`. -/
theorem hyperboloidInclusion_contMDiff (n : ℕ) (R : ℝ) [Fact (0 < R)] :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) ∞
      (hyperboloidInclusion n R) := by
  have h2 : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) ∞
      (hyperboloidLift n R) :=
    (contDiff_hyperboloidLift n R).contMDiff
  refine (h2.comp (contMDiff_hyperboloid_proj n R)).congr fun p => ?_
  show p.1 = hyperboloidLift n R p.1.1
  exact Prod.ext rfl (hyperboloid_sqrt_eq p).symm

/-- **Math.** The differential of the inclusion at `p`, as an explicit
continuous linear map: `u ↦ (u, ⟪p₁, u⟫ / p_t)`. The tangency relation
`v¹p¹ + ⋯ + vⁿpⁿ - v^{n+1}p^{n+1} = 0` of Petersen's proof is encoded in the
second component. -/
def hyperboloidInclusionDeriv (n : ℕ) (R : ℝ) (p : hyperboloid n R) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) × ℝ :=
  (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).prod
    ((p.1.2)⁻¹ • innerSL ℝ p.1.1)

@[simp]
theorem hyperboloidInclusionDeriv_apply (n : ℕ) (R : ℝ) (p : hyperboloid n R)
    (u : EuclideanSpace ℝ (Fin n)) :
    hyperboloidInclusionDeriv n R p u = (u, ⟪p.1.1, u⟫ / p.1.2) := by
  simp only [hyperboloidInclusionDeriv, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
    smul_eq_mul]
  rw [div_eq_inv_mul]

/-- **Math.** The inclusion has manifold derivative
`u ↦ (u, ⟪p₁, u⟫ / p_t)` at `p`: in the global chart the inclusion is the
parametrization `x ↦ (x, √(‖x‖² + R²))`, whose derivative at `p₁` is computed
by `hyperboloidLift_hasFDerivAt` and simplified using `√(‖p₁‖² + R²) = p_t`. -/
theorem hasMFDerivAt_hyperboloidInclusion (n : ℕ) (R : ℝ) [Fact (0 < R)]
    (p : hyperboloid n R) :
    HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
      (hyperboloidInclusion n R) p (hyperboloidInclusionDeriv n R p) := by
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  rw [ModelWithCorners.range_eq_univ, hasFDerivWithinAt_univ]
  have hne : ‖p.1.1‖ ^ 2 + R ^ 2 ≠ 0 := by
    rw [hyperboloid_norm_sq_add p]
    exact (pow_pos (hyperboloid_t_pos p) 2).ne'
  have hlift := hyperboloidLift_hasFDerivAt n R p.1.1 hne
  rw [hyperboloid_sqrt_eq p] at hlift
  exact hlift

/-- **Math.** The differential of the inclusion:
`Dι_p(u) = (u, ⟪p₁, u⟫ / p_t)`. -/
theorem mfderiv_hyperboloidInclusion (n : ℕ) (R : ℝ) [Fact (0 < R)]
    (p : hyperboloid n R) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
      (hyperboloidInclusion n R) p = hyperboloidInclusionDeriv n R p :=
  (hasMFDerivAt_hyperboloidInclusion n R p).mfderiv

/-- **Math.** The differential of the inclusion is injective: its first
component is the identity. -/
theorem mfderiv_hyperboloidInclusion_injective (n : ℕ) (R : ℝ) [Fact (0 < R)]
    (p : hyperboloid n R) :
    Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
        (hyperboloidInclusion n R) p) := by
  rw [mfderiv_hyperboloidInclusion]
  intro u v huv
  have h1 := congrArg Prod.fst huv
  simpa [hyperboloidInclusionDeriv] using h1

/-- **Math.** The inclusion `ι : H^n(R) → ℝ^{n,1}` is a smooth immersion. -/
theorem hyperboloidInclusion_isSmoothImmersion (n : ℕ) (R : ℝ) [Fact (0 < R)] :
    IsSmoothImmersion (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)) (hyperboloidInclusion n R) :=
  ⟨hyperboloidInclusion_contMDiff n R, mfderiv_hyperboloidInclusion_injective n R⟩

/-! ## Positivity of the induced form — the Cauchy–Schwarz computation

This is the displayed computation of Petersen's Example 1.1.7: for a tangent
vector `u` at `p ∈ H^n(R)` with ambient image `Dι(u) = (u, ⟪p₁, u⟫ / p_t)`,
the induced Minkowski square norm is

  `|Dι(u)|² = ‖u‖² - (⟪p₁, u⟫ / p_t)²`,

and by Cauchy–Schwarz, `⟪p₁, u⟫² ≤ ‖p₁‖² ‖u‖²`; since `‖p₁‖² = p_t² - R²`,

  `|Dι(u)|² ≥ ‖u‖² (R / p_t)² > 0` for `u ≠ 0`. -/

/-- **Math.** Petersen Example 1.1.7, the Cauchy–Schwarz positivity estimate:
the Minkowski square norm of `Dι_p(u) = (u, ⟪p₁, u⟫ / p_t)` is positive for
`u ≠ 0`, since `‖u‖² - (⟪p₁, u⟫ / p_t)² ≥ ‖u‖² (R / p_t)² > 0`. -/
theorem minkowskiForm_inclusionDeriv_pos (n : ℕ) (R : ℝ) [Fact (0 < R)]
    (p : hyperboloid n R) (u : EuclideanSpace ℝ (Fin n)) (hu : u ≠ 0) :
    0 < minkowskiForm (EuclideanSpace ℝ (Fin n)) ℝ
        (hyperboloidInclusionDeriv n R p u) (hyperboloidInclusionDeriv n R p u) := by
  have hR : 0 < R := Fact.out
  have hp2 : 0 < p.1.2 := hyperboloid_t_pos p
  have hpnorm : ‖p.1.1‖ ^ 2 = p.1.2 ^ 2 - R ^ 2 := by
    have h := hyperboloid_norm_sq_add p
    linarith
  rw [hyperboloidInclusionDeriv_apply, minkowskiForm_apply]
  set a := ⟪p.1.1, u⟫ with ha
  -- `|Dι(u)|² = ‖u‖² - (a / p_t)²`
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  -- Cauchy–Schwarz: `a² ≤ ‖p₁‖² ‖u‖² = (p_t² - R²) ‖u‖²`
  have hCS : a * a ≤ ‖p.1.1‖ ^ 2 * ‖u‖ ^ 2 := by
    have h := real_inner_mul_inner_self_le p.1.1 u
    rwa [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  rw [hpnorm] at hCS
  have hu2 : (0 : ℝ) < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu) 2
  have ht2 : (0 : ℝ) < p.1.2 ^ 2 := pow_pos hp2 2
  -- hence `a² < ‖u‖² p_t²`, i.e. `(a / p_t)² < ‖u‖²`
  have hkey : a ^ 2 < ‖u‖ ^ 2 * p.1.2 ^ 2 := by
    nlinarith [mul_pos (pow_pos hR 2) hu2]
  rw [div_pow, sub_pos, div_lt_iff₀ ht2]
  exact hkey

/-- **Math.** Positivity of the induced form, phrased for tangent vectors of
the hyperboloid: the pullback of the Minkowski metric along the inclusion is
positive definite (Petersen Example 1.1.7). -/
theorem hyperboloid_pullbackPseudoForm_pos (n : ℕ) (R : ℝ) [Fact (0 < R)]
    (p : hyperboloid n R) (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p)
    (hu : u ≠ 0) :
    0 < pullbackPseudoForm (minkowskiMetric (EuclideanSpace ℝ (Fin n)) ℝ)
        (hyperboloidInclusion n R) p u u := by
  rw [pullbackPseudoForm_apply, mfderiv_hyperboloidInclusion, minkowskiMetric_inner]
  exact minkowskiForm_inclusionDeriv_pos n R p u hu

/-! ## The hyperbolic metric -/

/-- **Math.** Petersen Example 1.1.7 — **hyperbolic space** `H^n(R)`. The
hyperbolic space `H^n(R) ⊂ ℝ^{n,1}` is the branch with `x^{n+1} > 0` of the
hyperboloid `(x¹)² + ⋯ + (xⁿ)² - (x^{n+1})² = -R²`, with the metric induced
from the Minkowski metric on `ℝ^{n,1}` (the pullback of `minkowskiMetric`
along the inclusion). This induced form is positive definite — by the
Cauchy–Schwarz computation `minkowskiForm_inclusionDeriv_pos` — hence a
genuine Riemannian metric on `H^n(R)`. When `R = 1` one writes `H^n` and calls
it hyperbolic `n`-space. -/
def hyperbolicSpace (n : ℕ) (R : ℝ) [Fact (0 < R)] :
    RiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (hyperboloid n R) where
  inner p := pullbackPseudoForm (minkowskiMetric (EuclideanSpace ℝ (Fin n)) ℝ)
    (hyperboloidInclusion n R) p
  symm p u v := pullbackPseudoForm_symm (minkowskiMetric (EuclideanSpace ℝ (Fin n)) ℝ)
    (hyperboloidInclusion n R) p u v
  pos p u hu := hyperboloid_pullbackPseudoForm_pos n R p u hu
  isVonNBounded p :=
    isVonNBounded_of_posDef (E := EuclideanSpace ℝ (Fin n))
      (pullbackPseudoForm (minkowskiMetric (EuclideanSpace ℝ (Fin n)) ℝ)
        (hyperboloidInclusion n R) p)
      (fun u hu => hyperboloid_pullbackPseudoForm_pos n R p u hu)
  contMDiff := pullbackPseudoForm_contMDiff (minkowskiMetric (EuclideanSpace ℝ (Fin n)) ℝ)
    (hyperboloidInclusion_contMDiff n R)

@[simp]
theorem hyperbolicSpace_metricInner (n : ℕ) (R : ℝ) [Fact (0 < R)]
    (p : hyperboloid n R)
    (u v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p) :
    (hyperbolicSpace n R).metricInner p u v
      = minkowskiForm (EuclideanSpace ℝ (Fin n)) ℝ
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
            (hyperboloidInclusion n R) p u)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
            (hyperboloidInclusion n R) p v) :=
  rfl

end PetersenLib
