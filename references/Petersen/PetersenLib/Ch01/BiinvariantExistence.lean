import PetersenLib.Ch01.MetricConstructions
import PetersenLib.Ch01.BiinvariantAveraging
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Existence of bi-invariant metrics on compact Lie groups (Petersen Ex. 1.6.24(1))

This file supplies the **manifold bridge** that turns the fixed-space averaging
engine `PetersenLib.CompactAveraging.avgForm` into an actual bi-invariant
Riemannian metric on a compact Lie group `G`, closing Petersen Exercise
1.6.24(1).

The mathematical route (an equivalent, cleaner substitute for Petersen's
"average the metric over right translations against the volume form", which
would need parametric integration of tensor *fields* on the manifold):

* Work on the fixed vector space `𝔤 = T_eG` (`= E`, the model space).  The
  **adjoint representation** `Ad_h = D(x ↦ hxh⁻¹)_e : 𝔤 → 𝔤` (`adMap`) is a
  continuous homomorphism into the invertible operators (`adMap_continuous`,
  `adMap_hom`, `adMap_injective`).
* Average *any* inner product `b₀` on `𝔤` over `Ad` against the normalised
  Haar (probability) measure of the compact group.  By the compact "unitary
  trick" (`avgForm_symm` / `avgForm_pos` / `avgForm_invariant`) the average
  `b` is a symmetric, positive-definite, `Ad`-**invariant** inner product.
* An `Ad`-invariant inner product on `𝔤` extends (via `leftInvariantMetric`)
  to a **bi-invariant** metric: left invariance is automatic
  (`leftInvariantMetric_isRiemannianIsometry`), and right invariance follows
  from `Ad`-invariance exactly as in the reverse direction of Exercise 1.6.25
  (`leftInvariantMetric_rightInvariant`).
-/

open MeasureTheory Bundle TopologicalSpace
open scoped ContDiff Manifold Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [IsManifold I ∞ G] [LieGroup I ∞ G]

namespace PetersenLib

/-! ## The adjoint representation `Ad : G → GL(𝔤)` -/

/-- **Math.** The **adjoint action** `Ad_h = D(conj_h)_e : 𝔤 → 𝔤` of `G` on its
Lie algebra `𝔤 = T_eG`, the differential at the identity of conjugation
`conj_h(y) = h y h⁻¹`. -/
def adMap (h : G) : E →L[ℝ] E := mfderiv I I (fun y => h * y * h⁻¹) 1

theorem adMap_apply (h : G) (u : TangentSpace I (1 : G)) :
    adMap (I := I) h u = mfderiv I I (fun y => h * y * h⁻¹) 1 u := rfl

/-- **Math.** Conjugation `conj_h : y ↦ h y h⁻¹` is smooth (hence
differentiable) at every point: it is `R_{h⁻¹} ∘ L_h`. -/
theorem mdifferentiableAt_conj (h p : G) :
    MDifferentiableAt I I (fun y => h * y * h⁻¹) p :=
  MDifferentiableAt.comp (I' := I) p
    (mdifferentiableAt_mul_right (I := I) (a := h⁻¹) (b := h * p))
    (mdifferentiableAt_mul_left (I := I) (a := h) (b := p))

/-- **Math.** The chain-rule identity underlying Exercises 1.6.24/1.6.25:
reading the differential of the right translation `R_h` through the
left-invariant trivializations at `x` and `xh` produces the adjoint map
`Ad_{h⁻¹}`: `d(L_{(xh)⁻¹})_{xh} ∘ d(R_h)_x = d(conj_{h⁻¹})_e ∘ d(L_{x⁻¹})_x`,
since `L_{(xh)⁻¹} ∘ R_h = conj_{h⁻¹} ∘ L_{x⁻¹}` as maps `G → G`. -/
theorem mfderiv_mul_right_conj (h x : G) (u : TangentSpace I x) :
    mfderiv I I ((x * h)⁻¹ * ·) (x * h) (mfderiv I I (· * h) x u)
      = mfderiv I I (fun y => h⁻¹ * y * h) 1 (mfderiv I I (x⁻¹ * ·) x u) := by
  have hconj : MDifferentiableAt I I (fun y => h⁻¹ * y * h) (x⁻¹ * x) :=
    MDifferentiableAt.comp (I' := I) (x⁻¹ * x)
      (mdifferentiableAt_mul_right (I := I) (a := h) (b := h⁻¹ * (x⁻¹ * x)))
      (mdifferentiableAt_mul_left (I := I) (a := h⁻¹) (b := x⁻¹ * x))
  have h1 : mfderiv I I (((x * h)⁻¹ * ·) ∘ (· * h)) x u
      = mfderiv I I ((x * h)⁻¹ * ·) (x * h) (mfderiv I I (· * h) x u) := by
    rw [mfderiv_comp x
      (mdifferentiableAt_mul_left (I := I) (a := (x * h)⁻¹) (b := x * h))
      (mdifferentiableAt_mul_right (I := I) (a := h) (b := x))]
    rfl
  have h2 : mfderiv I I ((fun y => h⁻¹ * y * h) ∘ (x⁻¹ * ·)) x u
      = mfderiv I I (fun y => h⁻¹ * y * h) (x⁻¹ * x)
          (mfderiv I I (x⁻¹ * ·) x u) := by
    rw [mfderiv_comp x hconj
      (mdifferentiableAt_mul_left (I := I) (a := x⁻¹) (b := x))]
    rfl
  have hfun : (((x * h)⁻¹ * ·) ∘ (· * h) : G → G)
      = ((fun y => h⁻¹ * y * h) ∘ (x⁻¹ * ·)) := by
    funext y
    show (x * h)⁻¹ * (y * h) = h⁻¹ * (x⁻¹ * y) * h
    rw [mul_inv_rev]
    group
  have hpt : (mfderiv I I (fun y => h⁻¹ * y * h) (x⁻¹ * x) :
        TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G))
      = mfderiv I I (fun y => h⁻¹ * y * h) 1 := by
    rw [inv_mul_cancel]
  rw [← h1, hfun, h2, hpt]
  rfl

/-- **Math.** `Ad_e = id`: conjugation by the identity is the identity map. -/
theorem adMap_one : adMap (I := I) (1 : G) = ContinuousLinearMap.id ℝ E := by
  have hfun : (fun y => (1 : G) * y * (1 : G)⁻¹) = (id : G → G) := by funext y; simp
  show mfderiv I I (fun y => (1 : G) * y * (1 : G)⁻¹) 1 = _
  rw [hfun, mfderiv_id]
  rfl

/-- **Math.** `Ad` is a **homomorphism**: `Ad_{gh} = Ad_g ∘ Ad_h`, because
`conj_{gh} = conj_g ∘ conj_h` and `conj_h(e) = e`. -/
theorem adMap_hom (g h : G) :
    adMap (I := I) (g * h) = (adMap (I := I) g).comp (adMap (I := I) h) := by
  have hcomp : (fun y => (g * h) * y * (g * h)⁻¹)
      = (fun y => g * y * g⁻¹) ∘ (fun y => h * y * h⁻¹) := by
    funext y
    show (g * h) * y * (g * h)⁻¹ = g * (h * y * h⁻¹) * g⁻¹
    rw [mul_inv_rev]; group
  have hpt : (fun y => h * y * h⁻¹) (1 : G) = (1 : G) := by simp
  have h1 : mfderiv I I (fun y => (g * h) * y * (g * h)⁻¹) 1
      = (mfderiv I I (fun y => g * y * g⁻¹) ((fun y => h * y * h⁻¹) (1 : G))).comp
          (mfderiv I I (fun y => h * y * h⁻¹) 1) := by
    rw [hcomp]
    exact mfderiv_comp 1 (mdifferentiableAt_conj g _) (mdifferentiableAt_conj h 1)
  show mfderiv I I (fun y => (g * h) * y * (g * h)⁻¹) 1 = _
  rw [h1, hpt]
  rfl

/-- **Math.** Each `Ad_h` is **injective** (indeed invertible, with inverse
`Ad_{h⁻¹}`): `Ad_{h⁻¹} ∘ Ad_h = Ad_e = id`. -/
theorem adMap_injective (h : G) : Function.Injective (adMap (I := I) h) := by
  have hinv : (adMap (I := I) h⁻¹).comp (adMap (I := I) h) = ContinuousLinearMap.id ℝ E := by
    rw [← adMap_hom, inv_mul_cancel, adMap_one]
  refine Function.LeftInverse.injective (g := adMap (I := I) h⁻¹) (fun u => ?_)
  have := congrArg (fun T : E →L[ℝ] E => T u) hinv
  simpa using this

/-- **Math.** `Ad : G → 𝔤 →L 𝔤` is **continuous**.  Conjugation
`(h, y) ↦ h y h⁻¹` is jointly smooth and fixes the identity `conj_h(e) = e`, so
the family lemma `ContMDiffAt.mfderiv` reads its `y`-differential at `e` through
the tangent-space trivialization *at the fixed point `e`*; because both the
source and target base points are the constant `e`, that trivialization is a
single fixed continuous linear isomorphism `T := trivializationAt E (TangentSpace
I) e`, so `inTangentCoordinates` collapses to conjugating `Ad_h` by the fixed
maps `C₁ = T.symmL e`, `C₂ = T.continuousLinearMapAt e`.  Undoing that fixed
conjugation (`C₁ ∘ C₂ = id`) recovers `Ad` as a continuous function. -/
theorem adMap_continuous : Continuous (adMap (I := I) (G := G)) := by
  set T := trivializationAt E (TangentSpace I) (1 : G) with hT
  have h1mem : (1 : G) ∈ T.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) (1 : G)
  -- The trivialization coordinate iso at the fixed base point `1`, read as maps
  -- on the model space `E` (`TangentSpace I 1` is definitionally `E`).
  set C₁ : E →L[ℝ] E := (T.symmL ℝ (1 : G) : E →L[ℝ] E) with hC₁
  set C₂ : E →L[ℝ] E := (T.continuousLinearMapAt ℝ (1 : G) : E →L[ℝ] E) with hC₂
  have hC₁C₂ : ∀ y : E, C₁ (C₂ y) = y := fun y =>
    T.symmL_continuousLinearMapAt h1mem y
  rw [continuous_iff_continuousAt]
  intro h₀
  -- Smoothness of the tangent-coordinate representation of `Ad` at `h₀`.
  have hf : ContMDiffAt (I.prod I) I ∞
      (Function.uncurry (fun h y : G => h * y * h⁻¹)) (h₀, (fun _ : G => (1 : G)) h₀) :=
    (contMDiffAt_fst.mul contMDiffAt_snd).mul contMDiffAt_fst.inv
  have hmn : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by simp
  have h0 := ContMDiffAt.mfderiv (fun h y : G => h * y * h⁻¹) (fun _ : G => (1 : G))
    hf contMDiffAt_const hmn
  have hbase : (fun x : G => (fun h y : G => h * y * h⁻¹) x ((fun _ : G => (1 : G)) x))
      = (fun _ : G => (1 : G)) := by funext x; simp
  rw [hbase] at h0
  -- The tangent-coordinate representation of `Ad`: a fixed conjugation of `Ad_h`.
  set Ψ := inTangentCoordinates I I (fun _ : G => (1 : G)) (fun _ : G => (1 : G))
    (fun h => adMap (I := I) h) h₀ with hΨ
  have hΨcont : ContinuousAt Ψ h₀ := h0.continuousAt
  have hΨval : ∀ h : G, Ψ h = C₂.comp ((adMap (I := I) h).comp C₁) := fun _ => rfl
  -- Undo the fixed conjugation: `Ad_h = C₁ ∘ (C₂ ∘ Ad_h ∘ C₁) ∘ C₂` since `C₁ ∘ C₂ = id`.
  have hEq : ∀ h : G, adMap (I := I) h = C₁.comp ((Ψ h).comp C₂) := by
    intro h
    ext u
    rw [hΨval h]
    simp only [ContinuousLinearMap.comp_apply, hC₁C₂]
  rw [continuousAt_congr (Filter.Eventually.of_forall hEq)]
  exact continuousAt_const.clm_comp (hΨcont.clm_comp continuousAt_const)

/-! ## A canonical positive-definite inner product on `𝔤` -/

section StdForm

variable [FiniteDimensional ℝ E]

/-- The bare bilinear map `⟨u, v⟩ = ∑ᵢ (eⁱ u)(eⁱ v)` in the coordinates of a
fixed basis of the finite-dimensional space `E`. -/
def stdBilinMap : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v => ∑ i, (Module.finBasis ℝ E).coord i u * (Module.finBasis ℝ E).coord i v)
    (fun u u' v => by simp [add_mul, Finset.sum_add_distrib, map_add])
    (fun c u v => by simp [Finset.mul_sum, mul_assoc, map_smul])
    (fun u v v' => by simp [mul_add, Finset.sum_add_distrib, map_add])
    (fun c u v => by simp [Finset.mul_sum, mul_left_comm, map_smul])

/-- **Math.** A **positive-definite symmetric** continuous bilinear form (inner
product) on the finite-dimensional real space `E`: the sum of squared basis
coordinates.  It serves as the arbitrary seed inner product to be `Ad`-averaged;
any inner product would do. -/
def stdForm : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap ∘ₗ
      stdBilinMap)

theorem stdForm_apply (u v : E) :
    stdForm u v = ∑ i, (Module.finBasis ℝ E).coord i u * (Module.finBasis ℝ E).coord i v := rfl

theorem stdForm_symm (u v : E) : stdForm (E := E) u v = stdForm v u := by
  rw [stdForm_apply, stdForm_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem stdForm_pos (u : E) (hu : u ≠ 0) : 0 < stdForm (E := E) u u := by
  rw [stdForm_apply]
  have hne : ∃ i, (Module.finBasis ℝ E).coord i u ≠ 0 := by
    by_contra hcon
    exact hu ((Module.finBasis ℝ E).forall_coord_eq_zero_iff.mp
      fun i => not_not.mp fun hi => hcon ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := hne
  refine Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  exact mul_self_pos.mpr hi

end StdForm

/-! ## Existence of an `Ad`-invariant inner product on `𝔤` -/

/-- **Math.** Petersen Exercise 1.6.24(1), algebraic core: on the Lie algebra
`𝔤 = T_eG` of a **compact** Lie group there is a symmetric, positive-definite,
`Ad`-invariant inner product, obtained by averaging the canonical inner product
`stdForm` over the adjoint action against the normalised Haar (probability)
measure — the compact "unitary trick".  Right invariance of the measure (needed
to reindex the averaging) is arranged by pushing the left Haar measure forward
along inversion. -/
theorem exists_adInvariant_innerProduct [CompactSpace G] [T2Space G] [FiniteDimensional ℝ E] :
    ∃ b : E →L[ℝ] E →L[ℝ] ℝ,
      (∀ u v : E, b u v = b v u) ∧
      (∀ u : E, u ≠ 0 → 0 < b u u) ∧
      (∀ (h : G) (u v : E),
        b (mfderiv I I (fun y => h * y * h⁻¹) 1 u) (mfderiv I I (fun y => h * y * h⁻¹) 1 v)
          = b u v) := by
  haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := I) (n := ∞)
  haveI : Nonempty G := ⟨1⟩
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  -- The normalised Haar (probability) measure, made right-invariant via inversion.
  haveI hprob₀ : IsProbabilityMeasure (Measure.haarMeasure (⊤ : PositiveCompacts G)) := by
    refine ⟨?_⟩
    rw [show (Set.univ : Set G) = ↑(⊤ : PositiveCompacts G) from PositiveCompacts.coe_top.symm]
    exact Measure.haarMeasure_self
  set μ : Measure G := (Measure.haarMeasure (⊤ : PositiveCompacts G)).inv with hμ
  haveI : μ.IsMulRightInvariant := by rw [hμ]; infer_instance
  haveI : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    rw [hμ, Measure.inv_apply, Set.inv_univ]
    exact hprob₀.measure_univ
  refine ⟨CompactAveraging.avgForm μ (adMap_continuous (I := I)) stdForm, ?_, ?_, ?_⟩
  · exact fun u v =>
      CompactAveraging.avgForm_symm μ (adMap_continuous (I := I)) stdForm_symm u v
  · exact fun u hu =>
      CompactAveraging.avgForm_pos μ (adMap_continuous (I := I)) (adMap_injective (I := I))
        stdForm_pos u hu
  · exact fun h u v =>
      CompactAveraging.avgForm_invariant μ (adMap_continuous (I := I)) (adMap_hom (I := I))
        stdForm h u v

end PetersenLib
