import PetersenLib.Ch01.DoublyWarpedSmoothness

/-!
# Petersen Ch. 1, §1.4.6 — higher-dimensional and generalized Hopf fibrations
(Examples 1.4.12–1.4.14)

Petersen's Example 1.4.12 considers `I × S^{2n+1} × S¹` with the doubly warped
metric `dt² + ρ²(t) ds²_{2n+1} + φ²(t) dθ²`, splits the round metric of the
odd sphere as `ds²_{2n+1} = h + g` into the Hopf-fibre direction `h` and its
orthogonal complement `g`, and lets the circle act by simultaneous rotation;
the quotient map onto `I × S^{2n+1}` is then a Riemannian submersion onto

  `dt² + ρ²(t) g + ((ρφ)²/(ρ² + φ²))(t) · h`.

Exactly as for Examples 1.4.10/1.4.11 (`hopfFibrationGeneralSubmersion`,
`hopfFibrationRevisited` in `PetersenLib.Ch01.DoublyWarpedSmoothness`), the
statements here are proved on a **coordinate / universal-cover model**: the
Hopf-fibre direction of `S^{2n+1}` is modelled by a linear coordinate `s`, its
orthogonal complement by an inner product space `F` (with `dim F = 2n`), so the
source is `ℝ × (ℝ × F) × ℝ` with `dt² + ρ²(t)(ds² + g_F) + φ²(t) dθ²` and the
quotient map is `(t, (s, y), θ) ↦ (t, (s − θ, y))`, the exact analogue of
Wilhelm's map `(t, θ₁, θ₂) ↦ (t, θ₁ − θ₂)` with the extra `F`-directions
carried along isometrically.

**What is proved** (`hopfFibrationHigherDim`): on this model the quotient map is
a Riemannian submersion from `dt² + ρ²(t)(ds² + g_F) + φ²(t) dθ²` onto
`dt² + ((ρφ)²/(ρ² + φ²))(t) ds² + ρ²(t) g_F`, for arbitrary warping functions
`ρ, φ` (including where they vanish — hence the possibly degenerate *forms*
`IsFormRiemannianSubmersion`). The specializations recorded are
`hopfFibrationSUTwoCoframe` (`dim F = 2`, Example 1.4.13: `h = (σ¹)²`,
`g = (σ²)² + (σ³)²` in the `SU(2)` coframe) and `generalizedHopfFibration`
(`ρ = sin`, `φ = cos`, Example 1.4.14, where the target coefficient becomes
`sin²(t)cos²(t)`, i.e. the target is `dt² + sin²(t)(g + cos²(t) h)`).

**What is NOT proved** (and must not be claimed from these statements): the
identification of the coordinate model with the genuine round sphere
`S^{2n+3} ⊂ ℂ^{n+2}` (the Hopf bundle `S^{2n+1} → ℂP^n` is nontrivial, so the
splitting `ds²_{2n+1} = h + g` is *not* globally a product `ℝ × F` — only the
pointwise/local model is captured here), the identification of the circle action
with complex scalar multiplication, the identification of the quotient with
`ℂP^{n+1}` or of the target form with the Fubini–Study metric, and, in
Example 1.4.13, the identification of `h, g` with the actual left-invariant
`SU(2)` coframe `σ¹, σ², σ³` on `S³`. Only the (local) Riemannian-submersion
computation is formalized; this is the same honest limitation as
`hopfFibrationRevisited`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Examples 1.4.12–1.4.14.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped ContDiff Manifold Topology

namespace PetersenLib

section HopfHigherDim

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **Math.** The model of the round metric of `S^{2n+1}` split along the Hopf
fibration: on `ℝ × F` (the `ℝ` factor being the Hopf-fibre direction, `F` the
orthogonal complement, `dim F = 2n`), the metric `ds² + g_F`, i.e. `h + g` in
Petersen's notation of Example 1.4.12. -/
def hopfSplitMetric : RiemannianMetric (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (ℝ × F) :=
  warpedProductMetric (innerProductSpaceMetric F) (fun _ => 1) (fun _ => 1)
    contDiff_const contDiff_const (fun _ => one_ne_zero) (fun _ => one_ne_zero)

/-- **Eng.** On `ℝ` the real inner product is multiplication (definitionally, with
the arguments swapped). -/
private theorem real_inner_mul (a b : ℝ) : (inner ℝ a b : ℝ) = b * a := rfl

/-- **Eng.** `hopfSplitMetric` in components: `(ds² + g_F)(u, v) =
u₁v₁ + ⟪u₂, v₂⟫`. -/
theorem hopfSplitMetric_apply (x : ℝ × F)
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) x) :
    (hopfSplitMetric F).metricInner x u v = u.1 * v.1 + (inner ℝ u.2 v.2 : ℝ) := by
  have hfstu : mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) Prod.fst x u = u.1 := by
    rw [mfderiv_fst]; rfl
  have hfstv : mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) Prod.fst x v = v.1 := by
    rw [mfderiv_fst]; rfl
  have hsndu : mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) 𝓘(ℝ, F) Prod.snd x u = u.2 := by
    rw [mfderiv_snd]; rfl
  have hsndv : mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) 𝓘(ℝ, F) Prod.snd x v = v.2 := by
    rw [mfderiv_snd]; rfl
  rw [hopfSplitMetric, warpedProductMetric_apply, warpedProductForm_apply,
    hfstu, hfstv, hsndu, hsndv]
  simp only [innerProductSpaceMetric_apply, real_inner_mul]
  ring

/-- **Math.** Petersen Example 1.4.12, the quotient map in the coordinate model:
the simultaneous rotation `(t, (s, y), θ) ↦ (t, (s − θ, y))` from
`ℝ × (ℝ × F) × ℝ` (model of `I × S^{2n+1} × S¹`, the middle `ℝ` being the
Hopf-fibre coordinate of `S^{2n+1}`) to `ℝ × ℝ × F` (model of `I × S^{2n+1}`).
For `F = 0` this is exactly `hopfSubmersionMap` of Example 1.4.11. -/
def hopfHigherSubmersionMap : ℝ × (ℝ × F) × ℝ → ℝ × ℝ × F :=
  fun q => (q.1, (q.2.1.1 - q.2.2, q.2.1.2))

variable {F}

/-- **Eng.** The `ℝ`-component of the Hopf-fibre coordinate, `q ↦ q.2.1.1`, has
differential `u ↦ u.2.1.1`. -/
theorem mfderiv_proj211_apply (p : ℝ × (ℝ × F) × ℝ)
    (u : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ))) p) :
    mfderiv (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ)
      (fun q : ℝ × (ℝ × F) × ℝ => q.2.1.1) p u = u.2.1.1 := by
  have hcomp : (fun q : ℝ × (ℝ × F) × ℝ => q.2.1.1) =
      (Prod.fst : ℝ × F → ℝ) ∘ (fun q : ℝ × (ℝ × F) × ℝ => q.2.1) := rfl
  have hf : MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ)
      (Prod.fst : ℝ × F → ℝ) p.2.1 := mdifferentiableAt_fst
  have hg : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (fun q : ℝ × (ℝ × F) × ℝ => q.2.1) p :=
    (((contMDiff_fst (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (J := 𝓘(ℝ, ℝ)) (n := ∞)).comp
      (contMDiff_snd (I := 𝓘(ℝ, ℝ))
        (J := (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)) (n := ∞))) p).mdifferentiableAt (by simp)
  rw [hcomp, mfderiv_comp p hf hg]
  simp only [ContinuousLinearMap.comp_apply]
  rw [mfderiv_proj21_apply, mfderiv_fst]
  rfl

/-- **Eng.** The `F`-component of `S^{2n+1}`, `q ↦ q.2.1.2`, has differential
`u ↦ u.2.1.2`. -/
theorem mfderiv_proj212_apply (p : ℝ × (ℝ × F) × ℝ)
    (u : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ))) p) :
    mfderiv (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, F)
      (fun q : ℝ × (ℝ × F) × ℝ => q.2.1.2) p u = u.2.1.2 := by
  have hcomp : (fun q : ℝ × (ℝ × F) × ℝ => q.2.1.2) =
      (Prod.snd : ℝ × F → F) ∘ (fun q : ℝ × (ℝ × F) × ℝ => q.2.1) := rfl
  have hf : MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) 𝓘(ℝ, F)
      (Prod.snd : ℝ × F → F) p.2.1 := mdifferentiableAt_snd
  have hg : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (fun q : ℝ × (ℝ × F) × ℝ => q.2.1) p :=
    (((contMDiff_fst (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (J := 𝓘(ℝ, ℝ)) (n := ∞)).comp
      (contMDiff_snd (I := 𝓘(ℝ, ℝ))
        (J := (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)) (n := ∞))) p).mdifferentiableAt (by simp)
  rw [hcomp, mfderiv_comp p hf hg]
  simp only [ContinuousLinearMap.comp_apply]
  rw [mfderiv_proj21_apply, mfderiv_snd]
  rfl

/-- **Eng.** The differential of `hopfHigherSubmersionMap` at any point is the
linear map `(a, (b, y), c) ↦ (a, (b − c, y))`. -/
theorem hopfHigherSubmersionMap_mfderiv_apply (p : ℝ × (ℝ × F) × ℝ)
    (u : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ))) p) :
    mfderiv (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
        (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))) (hopfHigherSubmersionMap F) p u =
      (u.1, (u.2.1.1 - u.2.2, u.2.1.2)) := by
  have hcm211 : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, ℝ) ∞ (fun q : ℝ × (ℝ × F) × ℝ => q.2.1.1) :=
    (contMDiff_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, F))).comp
      ((contMDiff_fst (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (J := 𝓘(ℝ, ℝ))).comp
        (contMDiff_snd (I := 𝓘(ℝ, ℝ))
          (J := (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ))))
  have hcm212 : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, F) ∞ (fun q : ℝ × (ℝ × F) × ℝ => q.2.1.2) :=
    (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, F))).comp
      ((contMDiff_fst (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (J := 𝓘(ℝ, ℝ))).comp
        (contMDiff_snd (I := 𝓘(ℝ, ℝ))
          (J := (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ))))
  have hcm22 : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, ℝ) ∞ (fun q : ℝ × (ℝ × F) × ℝ => q.2.2) :=
    (contMDiff_snd (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (J := 𝓘(ℝ, ℝ))).comp
      (contMDiff_snd (I := 𝓘(ℝ, ℝ))
        (J := (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
  have hd211 := (hcm211 p).mdifferentiableAt (by simp)
  have hd212 := (hcm212 p).mdifferentiableAt (by simp)
  have hd22 := (hcm22 p).mdifferentiableAt (by simp)
  have hdsub : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, ℝ) (fun q : ℝ × (ℝ × F) × ℝ => q.2.1.1 - q.2.2) p := hd211.sub hd22
  have hsubapp : mfderiv (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, ℝ) (fun q : ℝ × (ℝ × F) × ℝ => q.2.1.1 - q.2.2) p u
      = u.2.1.1 - u.2.2 := by
    show mfderiv (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ)
        ((fun q : ℝ × (ℝ × F) × ℝ => q.2.1.1) -
          (fun q : ℝ × (ℝ × F) × ℝ => q.2.2)) p u = u.2.1.1 - u.2.2
    rw [mfderiv_sub hd211 hd22, ← mfderiv_proj211_apply p u,
      ← mfderiv_proj22_apply (I₁ := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (I₂ := 𝓘(ℝ, ℝ)) p u]
    rfl
  have hfstapp : mfderiv (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, ℝ) (Prod.fst : ℝ × (ℝ × F) × ℝ → ℝ) p u = u.1 := by
    rw [mfderiv_fst]; rfl
  have key : mfderiv (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
      (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))) (hopfHigherSubmersionMap F) p =
      (mfderiv (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ)
          (Prod.fst : ℝ × (ℝ × F) × ℝ → ℝ) p).prod
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
          (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
          (fun q : ℝ × (ℝ × F) × ℝ => (q.2.1.1 - q.2.2, q.2.1.2)) p) :=
    mfderiv_prodMk mdifferentiableAt_fst (hdsub.prodMk hd212)
  have key2 : mfderiv (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
      (fun q : ℝ × (ℝ × F) × ℝ => (q.2.1.1 - q.2.2, q.2.1.2)) p =
      (mfderiv (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ)
          (fun q : ℝ × (ℝ × F) × ℝ => q.2.1.1 - q.2.2) p).prod
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, F)
          (fun q : ℝ × (ℝ × F) × ℝ => q.2.1.2) p) :=
    mfderiv_prodMk hdsub hd212
  rw [key, key2, ← hfstapp, ← hsubapp, ← mfderiv_proj212_apply p u]
  rfl

variable (F)

/-- **Eng.** The doubly warped form `dt² + ρ²(t)(ds² + g_F) + φ²(t) dθ²` on
`ℝ × (ℝ × F) × ℝ`, written out on components of tangent vectors. -/
theorem hopfHigherSourceForm_apply (ρ φ : ℝ → ℝ) (p : ℝ × (ℝ × F) × ℝ)
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ))) p) :
    doublyWarpedProductForm (hopfSplitMetric F) (innerProductSpaceMetric ℝ)
        ρ φ p u v =
      u.1 * v.1 +
        (ρ p.1 ^ 2 * (u.2.1.1 * v.2.1.1 + (inner ℝ u.2.1.2 v.2.1.2 : ℝ)) +
          φ p.1 ^ 2 * (u.2.2 * v.2.2)) := by
  have hfu : mfderiv (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, ℝ) Prod.fst p u = u.1 := by rw [mfderiv_fst]; rfl
  have hfv : mfderiv (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, ℝ) Prod.fst p v = v.1 := by rw [mfderiv_fst]; rfl
  rw [doublyWarpedProductForm_apply, hfu, hfv,
    mfderiv_proj21_apply (I₁ := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (I₂ := 𝓘(ℝ, ℝ)) p u,
    mfderiv_proj21_apply (I₁ := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (I₂ := 𝓘(ℝ, ℝ)) p v,
    mfderiv_proj22_apply (I₁ := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (I₂ := 𝓘(ℝ, ℝ)) p u,
    mfderiv_proj22_apply (I₁ := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (I₂ := 𝓘(ℝ, ℝ)) p v,
    hopfSplitMetric_apply]
  simp only [innerProductSpaceMetric_apply, real_inner_mul]
  ring

/-- **Eng.** The target form `dt² + σ²(t) ds² + ρ²(t) g_F` on `ℝ × ℝ × F`,
written out on components of tangent vectors. -/
theorem hopfHigherTargetForm_apply (σ ρ : ℝ → ℝ) (q : ℝ × ℝ × F)
    (x y : TangentSpace (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))) q) :
    doublyWarpedProductForm (innerProductSpaceMetric ℝ) (innerProductSpaceMetric F)
        σ ρ q x y =
      x.1 * y.1 +
        (σ q.1 ^ 2 * (x.2.1 * y.2.1) + ρ q.1 ^ 2 * (inner ℝ x.2.2 y.2.2 : ℝ)) := by
  have hfx : mfderiv (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)))
      𝓘(ℝ, ℝ) Prod.fst q x = x.1 := by rw [mfderiv_fst]; rfl
  have hfy : mfderiv (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)))
      𝓘(ℝ, ℝ) Prod.fst q y = y.1 := by rw [mfderiv_fst]; rfl
  rw [doublyWarpedProductForm_apply, hfx, hfy,
    mfderiv_proj21_apply (I₁ := 𝓘(ℝ, ℝ)) (I₂ := 𝓘(ℝ, F)) q x,
    mfderiv_proj21_apply (I₁ := 𝓘(ℝ, ℝ)) (I₂ := 𝓘(ℝ, F)) q y,
    mfderiv_proj22_apply (I₁ := 𝓘(ℝ, ℝ)) (I₂ := 𝓘(ℝ, F)) q x,
    mfderiv_proj22_apply (I₁ := 𝓘(ℝ, ℝ)) (I₂ := 𝓘(ℝ, F)) q y]
  simp only [innerProductSpaceMetric_apply, real_inner_mul]
  ring

/-- **Math.** Petersen Example 1.4.12 (the higher-dimensional Hopf fibration),
on the coordinate model. Write the round metric of `S^{2n+1}` as `h + g`, where
`h` is the square of the coframe field dual to the Hopf-fibre direction and `g`
its orthogonal complement, and model this splitting by `ℝ × F` (Hopf direction
`s`, complement `F` with `dim F = 2n`). On `ℝ × (ℝ × F) × ℝ` — the model of
`I × S^{2n+1} × S¹` — carry the doubly warped metric
`dt² + ρ²(t)(ds² + g_F) + φ²(t) dθ²`. Then the simultaneous-rotation quotient
map `(t, (s, y), θ) ↦ (t, (s − θ, y))` is a Riemannian submersion onto

  `dt² + ((ρφ)²/(ρ² + φ²))(t) ds² + ρ²(t) g_F`,

i.e. Petersen's `dt² + ρ²(t) g + (ρφ)²/(ρ² + φ²)(t) · h`. The `s, θ` part is the
three-variable computation of Example 1.4.11 (`hopfSubmersionMap`,
`hopfSubmersion_horizontal_algebra`); the `F`-directions, which are orthogonal
to the fibres of the circle action, are carried along isometrically with their
`ρ²(t)` warping.

**Scope.** As in `hopfFibrationRevisited`, this is a statement about the
coordinate/universal-cover model only: the identification of `ℝ × F` with the
genuine sphere `S^{2n+1}` (whose Hopf splitting is *not* a global product), of
the circle action with complex scalar multiplication, and of the target form with
the Fubini–Study metric on `ℂP^{n+1}` is **not** covered. -/
theorem hopfFibrationHigherDim (ρ φ : ℝ → ℝ) :
    IsFormRiemannianSubmersion
      (doublyWarpedProductForm (hopfSplitMetric F) (innerProductSpaceMetric ℝ) ρ φ)
      (doublyWarpedProductForm (innerProductSpaceMetric ℝ) (innerProductSpaceMetric F)
        (fun t => ρ t * φ t / Real.sqrt (ρ t ^ 2 + φ t ^ 2)) ρ)
      (hopfHigherSubmersionMap F) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Smoothness of `(t, (s, y), θ) ↦ (t, (s − θ, y))`.
    have hcm211 : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
        𝓘(ℝ, ℝ) ∞ (fun q : ℝ × (ℝ × F) × ℝ => q.2.1.1) :=
      (contMDiff_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, F))).comp
        ((contMDiff_fst (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (J := 𝓘(ℝ, ℝ))).comp
          (contMDiff_snd (I := 𝓘(ℝ, ℝ))
            (J := (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ))))
    have hcm212 : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
        𝓘(ℝ, F) ∞ (fun q : ℝ × (ℝ × F) × ℝ => q.2.1.2) :=
      (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, F))).comp
        ((contMDiff_fst (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (J := 𝓘(ℝ, ℝ))).comp
          (contMDiff_snd (I := 𝓘(ℝ, ℝ))
            (J := (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ))))
    have hcm22 : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
        𝓘(ℝ, ℝ) ∞ (fun q : ℝ × (ℝ × F) × ℝ => q.2.2) :=
      (contMDiff_snd (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (J := 𝓘(ℝ, ℝ))).comp
        (contMDiff_snd (I := 𝓘(ℝ, ℝ))
          (J := (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
    exact (contMDiff_fst (I := 𝓘(ℝ, ℝ))
      (J := (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ))).prodMk
        ((hcm211.sub hcm22).prodMk hcm212)
  · -- Surjectivity of `DQ(a, (b, y), c) = (a, (b − c, y))`: preimage `(a, (b, y), 0)`.
    intro p z
    refine ⟨show ℝ × (ℝ × F) × ℝ from (z.1, (z.2.1, z.2.2), 0), ?_⟩
    rw [hopfHigherSubmersionMap_mfderiv_apply]
    exact Prod.ext rfl (Prod.ext (sub_zero z.2.1) rfl)
  · -- The metric identity on vectors orthogonal to `ker DQ = {(0, (c, 0), c)}`.
    intro p u v hu _hv
    have hker : mfderiv (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)))
        (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))) (hopfHigherSubmersionMap F) p
        (show ℝ × (ℝ × F) × ℝ from (0, (1, 0), 1)) = 0 := by
      rw [hopfHigherSubmersionMap_mfderiv_apply]
      exact Prod.ext rfl (Prod.ext (sub_self 1) rfl)
    have hu' : ρ p.1 ^ 2 * u.2.1.1 + φ p.1 ^ 2 * u.2.2 = 0 := by
      have h := hu (show ℝ × (ℝ × F) × ℝ from (0, (1, 0), 1)) hker
      rw [hopfHigherSourceForm_apply] at h
      simpa using h
    rw [hopfHigherSourceForm_apply, hopfHigherSubmersionMap_mfderiv_apply p u,
      hopfHigherSubmersionMap_mfderiv_apply p v, hopfHigherTargetForm_apply]
    simp only [hopfHigherSubmersionMap]
    linear_combination
      hopfSubmersion_horizontal_algebra (ρ := ρ p.1) (φ := φ p.1) v.2.1.1 v.2.2 hu'

/-- **Math.** Petersen Example 1.4.13 (the `SU(2)` coframe case, `n = 1`): the
case `dim F = 2` of `hopfFibrationHigherDim`. Here the model of `S³` splits its
round metric as `h + g` with `h = (σ¹)²` the square of the coframe field dual to
the Hopf-fibre direction and `g = (σ²)² + (σ³)²` the complementary part of the
left-invariant `SU(2)` coframe `σ¹, σ², σ³`; on `I × S³ × S¹` with
`dt² + ρ²(t)((σ¹)² + (σ²)² + (σ³)²) + φ²(t) dθ²`, the simultaneous rotation
descends to the Riemannian submersion onto
`dt² + ρ²(t)((σ²)² + (σ³)²) + ((ρφ)²/(ρ² + φ²))(t)(σ¹)²`.

**Scope.** Only the coordinate-model submersion is proved (with `ℝ × ℝ²`
modelling the splitting `h ⊕ g` of `T S³`): the identification of the two
summands with the actual left-invariant coframe of `SU(2) ≅ S³`, and of the
model with the round `S³` itself, is **not** covered. -/
theorem hopfFibrationSUTwoCoframe (ρ φ : ℝ → ℝ) :
    IsFormRiemannianSubmersion
      (doublyWarpedProductForm (hopfSplitMetric (EuclideanSpace ℝ (Fin 2)))
        (innerProductSpaceMetric ℝ) ρ φ)
      (doublyWarpedProductForm (innerProductSpaceMetric ℝ)
        (innerProductSpaceMetric (EuclideanSpace ℝ (Fin 2)))
        (fun t => ρ t * φ t / Real.sqrt (ρ t ^ 2 + φ t ^ 2)) ρ)
      (hopfHigherSubmersionMap (EuclideanSpace ℝ (Fin 2))) :=
  hopfFibrationHigherDim (EuclideanSpace ℝ (Fin 2)) ρ φ

/-- **Math.** Petersen Example 1.4.14 (the generalized Hopf fibration): the case
`ρ = sin`, `φ = cos` on `I = (0, π/2)` of `hopfFibrationHigherDim`. Since
`(sin·cos)²/(sin² + cos²) = sin²(t)cos²(t)`, the target form is
`dt² + sin²(t)cos²(t) · h + sin²(t) · g = dt² + sin²(t)(g + cos²(t) h)`: on the
model of `I × S^{2n+1} × S¹` with `dt² + sin²(t) ds²_{2n+1} + cos²(t) dθ²`, the
simultaneous rotation is a Riemannian submersion onto that form (Petersen's
metric on the model of `ℂP^{n+1}`).

**Scope.** As for `hopfFibrationHigherDim` / `hopfFibrationRevisited`, this is
the coordinate-model statement: the identification of the source with the round
`S^{2n+3}`, of the quotient with `ℂP^{n+1}`, and of the target form with the
Fubini–Study metric is **not** covered. -/
theorem generalizedHopfFibration :
    IsFormRiemannianSubmersion
      (doublyWarpedProductForm (hopfSplitMetric F) (innerProductSpaceMetric ℝ)
        Real.sin Real.cos)
      (doublyWarpedProductForm (innerProductSpaceMetric ℝ) (innerProductSpaceMetric F)
        (fun t => Real.sin t * Real.cos t) Real.sin)
      (hopfHigherSubmersionMap F) := by
  have hfun : (fun t => Real.sin t * Real.cos t /
      Real.sqrt (Real.sin t ^ 2 + Real.cos t ^ 2)) =
      fun t => Real.sin t * Real.cos t := by
    funext t
    rw [Real.sin_sq_add_cos_sq, Real.sqrt_one, div_one]
  simpa only [hfun] using hopfFibrationHigherDim F Real.sin Real.cos

end HopfHigherDim

end PetersenLib
