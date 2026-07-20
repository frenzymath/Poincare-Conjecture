/-
Chapter 2, "Riemannian Metrics", Problem 2-16: **the fibre metric on `Λ^k T^*M`**.

Lee asks for the unique fibre metric `⟨·,·⟩_g` on the bundle `Λ^k T^*M` of a Riemannian
`n`-manifold `(M, g)` satisfying

  `⟨ω^1 ∧ ⋯ ∧ ω^k, η^1 ∧ ⋯ ∧ η^k⟩_g = det (⟨ω^i, η^j⟩_g)`                              (2.26)

whenever the `ω^i, η^j` are covectors at a point.  The two halves proved earlier are assembled
here into that statement:

* `LeeLib.Ch02.InnerForms` builds the *fibrewise algebra* on an abstract inner product space `V` —
  the form `innerForms e` on `V [⋀^ι]→L[ℝ] ℝ` determined by an orthonormal basis `e`, Lee's
  characterization (2.26), positive definiteness, uniqueness, and frame independence;
* `LeeLib.Ch02.InnerFormsBundle` supplies the *analytic* ingredient: a smooth `k`-form field
  applied to `k` smooth vector fields is a smooth function (`contMDiffAt_apply_section`).

The pointwise value `g.innerFormsAt x` is `innerForms` for the inner product that `g` installs on
`T_x M`, computed from `stdOrthonormalBasis` — a canonical choice, by frame independence
(`innerForms_eq_innerForms`).  Every statement below is phrased through `g` itself (`g.innerAt`,
`sharp g x`, orthonormality of a frame as `g.inner x (Y i x) (Y j x) = δ_ij`), so no caller ever
has to install the fibrewise inner product structure; this matches the phrasing of
`LeeLib.Ch02.VolumeForm` and `exists_orthonormalFrame_nhds`.

## Smoothness

A fibre metric in Lee's sense is a smoothly varying inner product on the fibres, and smoothness
here means: for smooth `k`-form fields `ω, η`, the function `x ↦ ⟨ω_x, η_x⟩_g` is smooth
(`contMDiff_innerFormsAt`).  The proof is where the frame hypothesis pays: near any `x₀`, Lee's
Proposition 2.8 (`exists_orthonormalFrame_nhds`) provides a smooth `g`-orthonormal frame `(Y_i)`,
against which

  `⟨ω_x, η_x⟩_g = (∑_{s : Fin k → Fin n} ω_x (Y_{s 1} x, …) · η_x (Y_{s k} x, …)) / k!`

(`innerFormsAt_eq_sum_frame`), and each summand is smooth by `contMDiffAt_apply_section`.

## Uniqueness

Uniqueness needs no smoothness at all: it is fibrewise, because the wedges of covectors span each
fibre (`span_range_wedgeCovectors`) and (2.26) prescribes the form on them.  The assembled
statement `riemannian_fiberMetric_forms` therefore quantifies the uniqueness over *all* fibrewise
bilinear forms satisfying (2.26), smooth or not, which is stronger than what Lee asks.
-/
import LeeLib.Ch02.InnerFormsBundle
import LeeLib.Ch02.MusicalIsomorphism

namespace LeeLib.Ch02

open Bundle Module InnerProductSpace
open scoped Manifold ContDiff InnerProductSpace Matrix

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {k : ℕ}

namespace RiemannianMetric

/-! ### The pointwise fibre metric -/

/-- **The fibre metric on `k`-covectors at `x`** (Lee, Problem 2-16): the inner product
`⟨ω, η⟩_g` on `Λ^k (T_x^* M)`, i.e. on `(TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ`.

The value is `LeeLib.Ch02.innerForms` for the inner product that `g` installs on `T_x M`,
computed from the canonical `stdOrthonormalBasis`; by frame independence
(`innerForms_eq_innerForms`) any `g`-orthonormal basis gives the same form, which is what
`innerFormsAt_eq_sum_frame` below says in `g`-language. -/
def innerFormsAt (g : RiemannianMetric I M) (x : M)
    (w θ : (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  innerForms (stdOrthonormalBasis ℝ (TangentSpace I x)) w θ

/-- The fibre metric bundled as a bilinear form — the shape the uniqueness statement is
quantified over. -/
def innerFormsAtₗ (g : RiemannianMetric I M) (x : M) :
    ((TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ]
      ((TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  innerFormsₗ (stdOrthonormalBasis ℝ (TangentSpace I x))

@[simp] theorem innerFormsAtₗ_apply (g : RiemannianMetric I M) (x : M)
    (w θ : (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) :
    g.innerFormsAtₗ x w θ = g.innerFormsAt x w θ := rfl

/-- The fibre metric bundled as a *continuous* bilinear form on the fibre.  Continuity comes from
`innerFormsCLM`, which is assembled from evaluation maps and so needs no norm on the tangent
space. -/
def innerFormsAtCLM (g : RiemannianMetric I M) (x : M) :
    ((TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ]
      ((TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  innerFormsCLM (⇑(stdOrthonormalBasis ℝ (TangentSpace I x)))

@[simp] theorem innerFormsAtCLM_apply (g : RiemannianMetric I M) (x : M)
    (w θ : (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) :
    g.innerFormsAtCLM x w θ = g.innerFormsAt x w θ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  exact innerFormsCLM_eq_innerForms (stdOrthonormalBasis ℝ (TangentSpace I x)) w θ

/-! ### `innerFormsAt` is an inner product on each fibre -/

theorem innerFormsAt_comm (g : RiemannianMetric I M) (x : M)
    (w θ : (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) :
    g.innerFormsAt x w θ = g.innerFormsAt x θ w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  exact innerForms_comm (stdOrthonormalBasis ℝ (TangentSpace I x)) w θ

theorem innerFormsAt_add_left (g : RiemannianMetric I M) (x : M)
    (w₁ w₂ θ : (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) :
    g.innerFormsAt x (w₁ + w₂) θ = g.innerFormsAt x w₁ θ + g.innerFormsAt x w₂ θ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  exact innerForms_add_left (stdOrthonormalBasis ℝ (TangentSpace I x)) w₁ w₂ θ

theorem innerFormsAt_smul_left (g : RiemannianMetric I M) (x : M) (c : ℝ)
    (w θ : (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) :
    g.innerFormsAt x (c • w) θ = c * g.innerFormsAt x w θ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  exact innerForms_smul_left (stdOrthonormalBasis ℝ (TangentSpace I x)) c w θ

theorem innerFormsAt_self_nonneg (g : RiemannianMetric I M) (x : M)
    (w : (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) :
    0 ≤ g.innerFormsAt x w w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  exact innerForms_self_nonneg (stdOrthonormalBasis ℝ (TangentSpace I x)) w

/-- **Positive definiteness of the fibre metric.**  With symmetry, bilinearity and
`innerFormsAt_self_nonneg`, this makes `g.innerFormsAt x` an inner product on
`Λ^k (T_x^* M)`. -/
theorem innerFormsAt_self_pos (g : RiemannianMetric I M) (x : M)
    {w : (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ} (hw : w ≠ 0) :
    0 < g.innerFormsAt x w w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  exact innerForms_self_pos (stdOrthonormalBasis ℝ (TangentSpace I x)) hw

/-! ### Lee's (2.26), and uniqueness -/

/-- **Lee's (2.26)**: `⟨ω^1 ∧ ⋯ ∧ ω^k, η^1 ∧ ⋯ ∧ η^k⟩_g = det (⟨ω^i, η^j⟩_g)` for covectors at
`x`.  The inner product of two covectors is `⟨a, b⟩_g = ⟨a^♯, b^♯⟩_g`, written out through
`sharp` so that the statement mentions only `g`. -/
theorem innerFormsAt_wedgeCovectors (g : RiemannianMetric I M) (x : M)
    (a b : Fin k → (TangentSpace I x →L[ℝ] ℝ)) :
    g.innerFormsAt x (wedgeCovectors a) (wedgeCovectors b)
      = (Matrix.of fun i j => g.innerAt x (sharp g x (a i)) (sharp g x (b j))).det := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  exact innerForms_wedgeCovectors (stdOrthonormalBasis ℝ (TangentSpace I x)) a b

/-- **Uniqueness in Lee's Problem 2-16, fibrewise**: a bilinear form on `Λ^k (T_x^* M)`
satisfying (2.26) *is* `g.innerFormsAt x`.  No smoothness enters: the wedges of covectors span
the fibre, and (2.26) prescribes the form on them. -/
theorem eq_innerFormsAt_of_wedgeCovectors (g : RiemannianMetric I M) (x : M)
    (B : ((TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ]
      ((TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (hB : ∀ a b : Fin k → (TangentSpace I x →L[ℝ] ℝ),
      B (wedgeCovectors a) (wedgeCovectors b)
        = (Matrix.of fun i j => g.innerAt x (sharp g x (a i)) (sharp g x (b j))).det) :
    B = g.innerFormsAtₗ x := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  exact eq_innerForms_of_wedgeCovectors (stdOrthonormalBasis ℝ (TangentSpace I x)) B hB

/-! ### The frame computation -/

/-- **The fibre metric computed against any local `g`-orthonormal frame**: for `x` in the domain
of a frame `(Y_i)` with `⟨Y_i, Y_j⟩_g = δ_ij`,

  `⟨ω, η⟩_g = (∑_{s : Fin k → Fin n} ω(Y_{s 1}|_x, …, Y_{s k}|_x) · η(Y_{s 1}|_x, …)) / k!`.

This is simultaneously the frame independence Lee asks to check — the right-hand side computes
`innerForms` for the orthonormal basis `(Y_i|_x)`, and the equality says the canonical
`stdOrthonormalBasis` value agrees with it — and the identity that the smoothness proof below
localizes through. -/
theorem innerFormsAt_eq_sum_frame (g : RiemannianMetric I M)
    {u : Set M} {Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x} {x : M}
    (hY : IsLocalFrameOn I E ∞ Y u)
    (hon : ∀ x ∈ u, ∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0)
    (hx : x ∈ u) (w θ : (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) :
    g.innerFormsAt x w θ
      = (∑ s : Fin k → Fin (finrank ℝ E),
          w (fun i => Y (s i) x) * θ (fun i => Y (s i) x)) / (Nat.factorial k) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have hon' := orthonormal_toBasisAt g hY hon hx
  have h1 : g.innerFormsAt x w θ
      = innerForms ((hY.toBasisAt hx).toOrthonormalBasis hon') w θ := by
    show innerForms (stdOrthonormalBasis ℝ (TangentSpace I x)) w θ = _
    rw [innerForms_eq_innerForms (stdOrthonormalBasis ℝ (TangentSpace I x))
      ((hY.toBasisAt hx).toOrthonormalBasis hon')]
  rw [h1, innerForms]
  simp only [Basis.coe_toOrthonormalBasis, IsLocalFrameOn.toBasisAt_coe, Fintype.card_fin]

/-! ### Smoothness: `innerFormsAt` is a *fibre metric* -/

/-- **The pairing of two smooth `k`-form fields against the fibre metric is smooth at `x₀`.**

This is the smoothness clause of "fibre metric" in Lee's Problem 2-16.  Near `x₀`, Lee's
Proposition 2.8 (`exists_orthonormalFrame_nhds`) provides a smooth `g`-orthonormal frame, against
which the pairing becomes the finite sum of `innerFormsAt_eq_sum_frame`; each summand is a smooth
`k`-form field applied to `k` smooth vector fields, which is smooth by
`contMDiffAt_apply_section`. -/
theorem contMDiffAt_innerFormsAt (g : RiemannianMetric I M)
    {w θ : ∀ x : M, (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ} {x₀ : M}
    (hw : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ)
        (E := fun x => (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) x (w x)) x₀)
    (hθ : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ)
        (E := fun x => (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) x (θ x)) x₀) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => g.innerFormsAt x (w x) (θ x)) x₀ := by
  obtain ⟨u, Y, hu, hx₀u, hY, hon⟩ := exists_orthonormalFrame_nhds g x₀
  have hYs : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E (E := TangentSpace I) x (Y i x)) x₀ := fun i =>
    hY.contMDiffAt hu hx₀u i
  have hcand : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x => (∑ s : Fin k → Fin (finrank ℝ E),
        w x (fun i => Y (s i) x) * θ x (fun i => Y (s i) x)) * ((Nat.factorial k : ℝ))⁻¹) x₀ := by
    refine ContMDiffAt.mul ?_ contMDiffAt_const
    refine ContMDiffAt.sum fun s _ => ?_
    exact (contMDiffAt_apply_section hw fun i => hYs (s i)).mul
      (contMDiffAt_apply_section hθ fun i => hYs (s i))
  refine hcand.congr_of_eventuallyEq ?_
  filter_upwards [hu.mem_nhds hx₀u] with x hx
  rw [innerFormsAt_eq_sum_frame g hY hon hx, div_eq_mul_inv]

/-- **The pairing of two smooth `k`-form fields against the fibre metric is smooth** — the
smoothness clause of "fibre metric" in Lee's Problem 2-16, globally. -/
theorem contMDiff_innerFormsAt (g : RiemannianMetric I M)
    {w θ : ∀ x : M, (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ}
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ)
        (E := fun x => (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) x (w x)))
    (hθ : ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ)
        (E := fun x => (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) x (θ x))) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => g.innerFormsAt x (w x) (θ x)) := fun x₀ =>
  contMDiffAt_innerFormsAt g (hw x₀) (hθ x₀)

/-! ### Lee's Problem 2-16 itself -/

/-- **Lee, Problem 2-16 — the fibre metric on `Λ^k T^* M`.**

There is a *unique* family of bilinear forms on the fibres of `Λ^k T^* M` satisfying Lee's (2.26)
against wedges of covectors at each point.  Existence is `innerFormsAt`; that it is a *fibre
metric* — an inner product on each fibre, varying smoothly — is `innerFormsAt_comm`,
`innerFormsAt_self_pos` and `contMDiff_innerFormsAt`; uniqueness is fibrewise
(`eq_innerFormsAt_of_wedgeCovectors`), so it holds among *all* fibrewise bilinear forms
satisfying (2.26), with no smoothness assumed. -/
theorem riemannian_fiberMetric_forms (g : RiemannianMetric I M) (k : ℕ) :
    ∃! B : ∀ x : M, ((TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ]
        ((TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ℝ,
      ∀ (x : M) (a b : Fin k → (TangentSpace I x →L[ℝ] ℝ)),
        B x (wedgeCovectors a) (wedgeCovectors b)
          = (Matrix.of fun i j => g.innerAt x (sharp g x (a i)) (sharp g x (b j))).det := by
  refine ⟨fun x => g.innerFormsAtₗ x, fun x a b => ?_, fun B hB => funext fun x =>
    eq_innerFormsAt_of_wedgeCovectors g x (B x) (hB x)⟩
  rw [innerFormsAtₗ_apply]
  exact innerFormsAt_wedgeCovectors g x a b

end RiemannianMetric

end

end LeeLib.Ch02
