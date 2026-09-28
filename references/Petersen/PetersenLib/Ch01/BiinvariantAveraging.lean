import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Averaging a bilinear form over a compact-group action

Let `V` be a finite-dimensional real normed space, `K` a compact group with a
right-invariant probability measure `μ` (the normalised Haar measure), and
`ρ : K → (V →L[ℝ] V)` a continuous family of operators.  Given a bilinear form
`b₀ : V →L[ℝ] V →L[ℝ] ℝ`, its **average**

`avgForm μ hρ b₀  :  (x, y) ↦ ∫_K b₀(ρ g x, ρ g y) dμ(g)`

is again a bilinear form (`avgForm_apply`).  When `ρ` is a homomorphism into the
invertible operators and `b₀` is a symmetric positive-definite inner product,
the average is:

* symmetric  (`avgForm_symm`),
* positive definite  (`avgForm_pos`), and
* `ρ`-**invariant**: `avgForm(ρ h x, ρ h y) = avgForm(x, y)`  (`avgForm_invariant`).

This is the compact version of the "unitary trick": a compact group
representation always preserves an inner product.  Mathlib only provides the
*finite*-group version (`Representation.averageMap`); this file supplies the
compact-group version via the Bochner integral.

The construction stays entirely on the *fixed* space `V` — no manifold or
tangent-bundle integration is involved — which is exactly what makes it usable
as the algebraic engine behind Petersen §1.3 Exercise 1.6.24(1): a compact Lie
group admits a bi-invariant metric.  One takes `V = 𝔤 = T_eG`, `ρ = Ad`, and
`b₀` any inner product; `avgForm` produces an `Ad`-invariant inner product on
`𝔤`, which extends (via `leftInvariantMetric`) to a bi-invariant metric.

## Implementation note

Bochner integration of `V →L[ℝ] V →L[ℝ] ℝ`-valued functions is blocked in the
current Mathlib by a missing `ContinuousENorm (V →L[ℝ] V →L[ℝ] ℝ)` instance for
the doubly-iterated operator-norm space.  We therefore integrate the *scalar*
integrand `g ↦ b₀ (ρ g x) (ρ g y)` and assemble the result into a continuous
bilinear form using finite-dimensionality (`LinearMap.toContinuousLinearMap`).
-/

open MeasureTheory

namespace PetersenLib.CompactAveraging

set_option linter.unusedSectionVars false

variable {K : Type*} [Group K] [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableMul K]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The scalar integrand `g ↦ b₀ (ρ g x) (ρ g y)` is integrable: it is
continuous on the compact space `K` against a finite measure. -/
theorem scalarIntegrable {μ : Measure K} [IsFiniteMeasure μ] {ρ : K → (V →L[ℝ] V)}
    (hρ : Continuous ρ) (b₀ : V →L[ℝ] V →L[ℝ] ℝ) (x y : V) :
    Integrable (fun g => b₀ (ρ g x) (ρ g y)) μ :=
  ((continuous_const.clm_apply (hρ.clm_apply continuous_const)).clm_apply
    (hρ.clm_apply continuous_const)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The averaged form as a (bare) bilinear map: bilinearity comes from linearity
of the integral together with linearity of `b₀` and each `ρ g`. -/
noncomputable def avgBilinMap (μ : Measure K) [IsFiniteMeasure μ] {ρ : K → (V →L[ℝ] V)}
    (hρ : Continuous ρ) (b₀ : V →L[ℝ] V →L[ℝ] ℝ) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∫ g, b₀ (ρ g x) (ρ g y) ∂μ)
    (fun x x' y => by
      rw [← integral_add (scalarIntegrable hρ b₀ x y) (scalarIntegrable hρ b₀ x' y)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun g => by simp [map_add]))
    (fun c x y => by
      rw [← integral_smul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun g => by simp [map_smul]))
    (fun x y y' => by
      rw [← integral_add (scalarIntegrable hρ b₀ x y) (scalarIntegrable hρ b₀ x y')]
      exact integral_congr_ae (Filter.Eventually.of_forall fun g => by simp [map_add]))
    (fun c x y => by
      rw [← integral_smul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun g => by simp [map_smul]))

/-- The **averaged bilinear form** `avgForm μ hρ b₀ : V →L[ℝ] V →L[ℝ] ℝ`,
obtained from `avgBilinMap` by promoting it to a continuous bilinear form (every
bilinear map on a finite-dimensional space is continuous). -/
noncomputable def avgForm (μ : Measure K) [IsFiniteMeasure μ] {ρ : K → (V →L[ℝ] V)}
    (hρ : Continuous ρ) (b₀ : V →L[ℝ] V →L[ℝ] ℝ) : V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ
      avgBilinMap μ hρ b₀)

@[simp]
theorem avgForm_apply (μ : Measure K) [IsFiniteMeasure μ] {ρ : K → (V →L[ℝ] V)}
    (hρ : Continuous ρ) (b₀ : V →L[ℝ] V →L[ℝ] ℝ) (x y : V) :
    avgForm μ hρ b₀ x y = ∫ g, b₀ (ρ g x) (ρ g y) ∂μ := rfl

/-- The averaged form is symmetric whenever the seed form `b₀` is. -/
theorem avgForm_symm (μ : Measure K) [IsFiniteMeasure μ] {ρ : K → (V →L[ℝ] V)}
    (hρ : Continuous ρ) {b₀ : V →L[ℝ] V →L[ℝ] ℝ} (hb : ∀ u v : V, b₀ u v = b₀ v u)
    (x y : V) :
    avgForm μ hρ b₀ x y = avgForm μ hρ b₀ y x := by
  rw [avgForm_apply, avgForm_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g => hb _ _)

/-- The averaged form is positive definite when the seed form `b₀` is and every
`ρ g` is injective: the continuous, strictly positive integrand attains a
positive minimum on the compact group, giving a positive lower bound for the
integral against the probability measure. -/
theorem avgForm_pos (μ : Measure K) [IsProbabilityMeasure μ] {ρ : K → (V →L[ℝ] V)}
    (hρ : Continuous ρ) (hinj : ∀ g, Function.Injective (ρ g))
    {b₀ : V →L[ℝ] V →L[ℝ] ℝ} (hbpos : ∀ u : V, u ≠ 0 → 0 < b₀ u u)
    (x : V) (hx : x ≠ 0) :
    0 < avgForm μ hρ b₀ x x := by
  rw [avgForm_apply]
  have hgx : Continuous (fun g => ρ g x) := hρ.clm_apply continuous_const
  have hfc : Continuous (fun g => b₀ (ρ g x) (ρ g x)) :=
    (continuous_const.clm_apply hgx).clm_apply hgx
  have hfpos : ∀ g, 0 < b₀ (ρ g x) (ρ g x) := fun g =>
    hbpos _ (fun h => hx (hinj g (by simpa using h)))
  obtain ⟨g₀, -, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hfc.continuousOn
  have hint : Integrable (fun g => b₀ (ρ g x) (ρ g x)) μ := scalarIntegrable hρ b₀ x x
  have hle : (fun _ : K => b₀ (ρ g₀ x) (ρ g₀ x)) ≤ fun g => b₀ (ρ g x) (ρ g x) :=
    fun g => (isMinOn_iff.mp hmin) g (Set.mem_univ g)
  have hchain : b₀ (ρ g₀ x) (ρ g₀ x) ≤ ∫ g, b₀ (ρ g x) (ρ g x) ∂μ := by
    have hmono := integral_mono (integrable_const _) hint hle
    simpa [integral_const, measure_univ] using hmono
  exact lt_of_lt_of_le (hfpos g₀) hchain

/-- The averaged form is `ρ`-**invariant** when `ρ` is a homomorphism into the
operator algebra and `μ` is right invariant: reindexing `g ↦ gh` uses the
homomorphism property `ρ (g h) = ρ g ∘ ρ h` and right invariance of the Haar
measure. -/
theorem avgForm_invariant (μ : Measure K) [IsFiniteMeasure μ] [μ.IsMulRightInvariant]
    {ρ : K → (V →L[ℝ] V)} (hρ : Continuous ρ)
    (hmul : ∀ g h : K, ρ (g * h) = (ρ g).comp (ρ h))
    (b₀ : V →L[ℝ] V →L[ℝ] ℝ) (h : K) (x y : V) :
    avgForm μ hρ b₀ (ρ h x) (ρ h y) = avgForm μ hρ b₀ x y := by
  rw [avgForm_apply, avgForm_apply]
  have key : ∀ g, b₀ (ρ g (ρ h x)) (ρ g (ρ h y)) = b₀ (ρ (g * h) x) (ρ (g * h) y) := by
    intro g; simp only [hmul g h, ContinuousLinearMap.comp_apply]
  calc ∫ g, b₀ (ρ g (ρ h x)) (ρ g (ρ h y)) ∂μ
        = ∫ g, b₀ (ρ (g * h) x) (ρ (g * h) y) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall key)
    _ = ∫ g, b₀ (ρ g x) (ρ g y) ∂μ :=
          integral_mul_right_eq_self (fun g => b₀ (ρ g x) (ρ g y)) h

/-! ## Averaging an arbitrary continuous family of bilinear forms

The `avgForm` engine above assumes the family of forms arises from a *fixed* seed
`b₀` pulled back along a representation `ρ : K → (V →L[ℝ] V)` on the fixed space
`V`, i.e. `g ↦ b₀(ρ g ·, ρ g ·)`.  The averaging construction in fact only needs a
**family of bilinear forms** `β : K → (V →L[ℝ] V →L[ℝ] ℝ)` whose seed is allowed to
vary with `g`.  This is exactly what Petersen Exercise 1.6.26 needs *fibrewise*: at
a point `p` of the manifold the family is `γ ↦ (γ^*g₀)_p`, whose seed `g₀` sits at
the **moving** point `γ · p`, so it is not `b₀(ρ g ·, ρ g ·)` for any fixed `b₀`.

Only per-slice integrability of `g ↦ β g x y` is needed to define the average;
positive-definiteness needs, in addition, continuity of the diagonal slices
`g ↦ β g x x` (to extract a positive minimum on the compact `K`). -/

section Family

/-- If the whole family `β` is continuous, each scalar slice `g ↦ β g x y` is
integrable on the compact `K` against a finite measure. -/
theorem familyIntegrable (μ : Measure K) [IsFiniteMeasure μ] {β : K → (V →L[ℝ] V →L[ℝ] ℝ)}
    (hβ : Continuous β) (x y : V) :
    Integrable (fun g => β g x y) μ :=
  ((hβ.clm_apply continuous_const).clm_apply continuous_const).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The averaged family form as a (bare) bilinear map: bilinearity comes from
linearity of the integral together with linearity of each `β g`. -/
noncomputable def avgFamilyBilinMap (μ : Measure K) [IsFiniteMeasure μ]
    (β : K → (V →L[ℝ] V →L[ℝ] ℝ))
    (hint : ∀ x y : V, Integrable (fun g => β g x y) μ) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∫ g, β g x y ∂μ)
    (fun x x' y => by
      rw [← integral_add (hint x y) (hint x' y)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun g => by simp [map_add]))
    (fun c x y => by
      rw [← integral_smul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun g => by simp [map_smul]))
    (fun x y y' => by
      rw [← integral_add (hint x y) (hint x y')]
      exact integral_congr_ae (Filter.Eventually.of_forall fun g => by simp [map_add]))
    (fun c x y => by
      rw [← integral_smul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun g => by simp [map_smul]))

/-- The **averaged family form** `avgFormFamily μ β hint : V →L[ℝ] V →L[ℝ] ℝ`,
`(x, y) ↦ ∫_K β g x y dμ(g)`, obtained from `avgFamilyBilinMap` by promoting it to
a continuous bilinear form (every bilinear map on a finite-dimensional space is
continuous). -/
noncomputable def avgFormFamily (μ : Measure K) [IsFiniteMeasure μ]
    (β : K → (V →L[ℝ] V →L[ℝ] ℝ))
    (hint : ∀ x y : V, Integrable (fun g => β g x y) μ) : V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ
      avgFamilyBilinMap μ β hint)

@[simp]
theorem avgFormFamily_apply (μ : Measure K) [IsFiniteMeasure μ] (β : K → (V →L[ℝ] V →L[ℝ] ℝ))
    (hint : ∀ x y : V, Integrable (fun g => β g x y) μ) (x y : V) :
    avgFormFamily μ β hint x y = ∫ g, β g x y ∂μ := rfl

/-- The averaged family form is symmetric whenever every `β g` is. -/
theorem avgFormFamily_symm (μ : Measure K) [IsFiniteMeasure μ] {β : K → (V →L[ℝ] V →L[ℝ] ℝ)}
    (hint : ∀ x y : V, Integrable (fun g => β g x y) μ)
    (hsymm : ∀ (g : K) (u v : V), β g u v = β g v u) (x y : V) :
    avgFormFamily μ β hint x y = avgFormFamily μ β hint y x := by
  rw [avgFormFamily_apply, avgFormFamily_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g => hsymm g x y)

/-- The averaged family form is positive definite when every `β g` is and the
diagonal slice `g ↦ β g x x` is continuous: the strictly positive, continuous
integrand attains a positive minimum on the compact group, giving a positive lower
bound for the integral against the probability measure. -/
theorem avgFormFamily_pos (μ : Measure K) [IsProbabilityMeasure μ] {β : K → (V →L[ℝ] V →L[ℝ] ℝ)}
    (hint : ∀ x y : V, Integrable (fun g => β g x y) μ)
    (hcont : ∀ x : V, Continuous (fun g => β g x x))
    (hpos : ∀ (g : K) (u : V), u ≠ 0 → 0 < β g u u) (x : V) (hx : x ≠ 0) :
    0 < avgFormFamily μ β hint x x := by
  rw [avgFormFamily_apply]
  obtain ⟨g₀, -, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty (hcont x).continuousOn
  have hle : (fun _ : K => β g₀ x x) ≤ fun g => β g x x :=
    fun g => (isMinOn_iff.mp hmin) g (Set.mem_univ g)
  have hchain : β g₀ x x ≤ ∫ g, β g x x ∂μ := by
    have hmono := integral_mono (integrable_const _) (hint x x) hle
    simpa [integral_const, measure_univ] using hmono
  exact lt_of_lt_of_le (hpos g₀ x hx) hchain

end Family

end PetersenLib.CompactAveraging
