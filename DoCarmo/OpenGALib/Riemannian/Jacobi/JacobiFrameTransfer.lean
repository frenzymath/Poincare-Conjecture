import OpenGALib.Riemannian.Jacobi.FrameReduction
import OpenGALib.Riemannian.Jacobi.PairJacobiField

/-!
# The frame-coefficient Jacobi transfer (do Carmo Ch. 8, `thm:dc-ch8-2-1`)

This file formalizes the **analytic heart of E. Cartan's theorem** (do Carmo Ch. 8,
`thm:dc-ch8-2-1`).  In Cartan's proof one has two geodesics — `γ` on `M` and
`γ̃` on `M̃` — carrying parallel orthonormal frames `eᵢ(t)` and `ẽᵢ(t)` with
`eₙ = γ'`, `ẽₙ = γ̃'`, related by the parallel-transport conjugation
`ẽᵢ(t) = φ_t(eᵢ(t))`.  A candidate Jacobi field is written in each frame with the
**same** scalar coefficients,

  `J(t) = Σᵢ yᵢ(t) eᵢ(t)`,   `J̃(t) = Σᵢ yᵢ(t) ẽᵢ(t)`,

and do Carmo argues: *since the curvature coefficients agree,*

  `⟨R(eₙ,eᵢ)eₙ,eⱼ⟩ = ⟨R̃(ẽₙ,ẽᵢ)ẽₙ,ẽⱼ⟩`,

*`J̃` satisfies the same second-order system as `J`, hence `J̃` is a Jacobi field
along `γ̃`.*

`jacobiFrameTransfer` is exactly this step, read in the two fixed charts.  It is
assembled from the two directions of the frame reduction already in the library:

* `frameJacobiComponent` (forward): a Jacobi field `J = Σ yᵢ eᵢ` on `M` yields the
  scalar system `yⱼ'' + Σᵢ aᵢⱼ yᵢ = 0`, `aᵢⱼ = ⟨R(eᵢ),eⱼ⟩`;
* the curvature-matching hypothesis replaces `aᵢⱼ` (on `M`) by the identical
  coefficients (on `M̃`);
* `covariantDerivCoord2_add_map_frameCombination_expand` (converse): the same scalar
  system forces `D²J̃/dt² + R̃(J̃) = 0`, i.e. `J̃ = Σ yᵢ ẽᵢ` is a Jacobi field on `M̃`.

The curvature operator is the Jacobi endomorphism `chartCurvatureEndo g α (u t) u̇(t)`
of `OpenGALib/Riemannian/Jacobi/PairJacobiField.lean` (`X ↦ ℛ(X, u̇)u̇`), so the
matching hypothesis is literally do Carmo's `⟨R(eₙ,eᵢ)eₙ,eⱼ⟩ = ⟨R̃(ẽₙ,ẽᵢ)ẽₙ,ẽⱼ⟩`
with `eₙ = u̇`.

Everything here is chart-local (fixed charts `α` on `M`, `α'` on `M̃`) and pointwise
in the geodesic parameter `t`; the construction of the parallel frames and the
conjugation `φ_t`, and the assembly with `cor:dc-ch5-2-5` into the local isometry
`f = exp_{p̃} ∘ i ∘ exp_p^{-1}`, are the remaining (chart-independent) steps of
`thm:dc-ch8-2-1`.

Blueprint: `lem:dc-ch8-2-1-jacobi-transfer`, `thm:dc-ch8-2-1`.
-/

open Set
open scoped Manifold Topology ContDiff NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** do Carmo Ch. 8, `thm:dc-ch8-2-1` (E. Cartan), the analytic heart.

Let `γ` be a geodesic on `M` read in the fixed chart `α` as `u`, and `γ̃` a geodesic
on `M̃` read in the fixed chart `α'` as `ū`.  Let `e₁,…,eₙ` be a parallel orthonormal
frame along `γ` and `ẽ₁,…,ẽₙ` a parallel orthonormal frame along `γ̃` (`n = dim M`),
and let `y₁,…,yₙ : ℝ → ℝ` be scalar coefficient functions.  Suppose:

* `J = Σᵢ yᵢ eᵢ` is a Jacobi field along `γ` at `t`
  (`D²J/dt² + ℛ(J, u̇)u̇ = 0`), and
* the two frames have matching curvature coefficients at `t`,
  `⟨ℛ(eᵢ, u̇)u̇, eⱼ⟩ = ⟨ℛ(ẽᵢ, ū̇)ū̇, ẽⱼ⟩` for all `i, j`
  (do Carmo's `⟨R(eₙ,eᵢ)eₙ,eⱼ⟩ = ⟨R̃(ẽₙ,ẽᵢ)ẽₙ,ẽⱼ⟩`, with `eₙ = u̇`).

Then `J̃ = Σᵢ yᵢ ẽᵢ` satisfies the same Jacobi equation along `γ̃` at `t`
(`D²J̃/dt² + ℛ̃(J̃, ū̇)ū̇ = 0`): the field with the *same* frame coefficients is a
Jacobi field on `M̃`. -/
theorem jacobiFrameTransfer {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (g : RiemannianMetric I M) (g' : RiemannianMetric I' M')
    (α : M) (α' : M') (u ubar : ℝ → E) (y : ι → ℝ → ℝ) (e ebar : ι → ℝ → E) {t : ℝ}
    (hf : ∀ i, ∀ᶠ r in 𝓝 t, DifferentiableAt ℝ (y i) r)
    (hf2 : ∀ i, DifferentiableAt ℝ (deriv (y i)) t)
    (he : ∀ i, ∀ᶠ r in 𝓝 t, DifferentiableAt ℝ (e i) r)
    (hpar : ∀ i, ∀ᶠ r in 𝓝 t, covariantDerivCoord (I := I) g α u (e i) r = 0)
    (horth : ∀ i j, chartMetricInner (I := I) g α (u t) (e i t) (e j t)
      = if i = j then (1 : ℝ) else 0)
    (hjac : covariantDerivCoord (I := I) g α u
          (fun r => covariantDerivCoord (I := I) g α u (fun s => ∑ i, y i s • e i s) r) t
        + chartCurvatureEndo (I := I) g α (u t) (deriv u t) (∑ i, y i t • e i t) = 0)
    (hebar : ∀ i, ∀ᶠ r in 𝓝 t, DifferentiableAt ℝ (ebar i) r)
    (hparbar : ∀ i, ∀ᶠ r in 𝓝 t, covariantDerivCoord (I := I') g' α' ubar (ebar i) r = 0)
    (hcardbar : Fintype.card ι = Module.finrank ℝ E)
    (horthbar : ∀ i j, chartMetricInner (I := I') g' α' (ubar t) (ebar i t) (ebar j t)
      = if i = j then (1 : ℝ) else 0)
    (hmatch : ∀ i j,
      chartMetricInner (I := I) g α (u t)
          (chartCurvatureEndo (I := I) g α (u t) (deriv u t) (e i t)) (e j t)
        = chartMetricInner (I := I') g' α' (ubar t)
          (chartCurvatureEndo (I := I') g' α' (ubar t) (deriv ubar t) (ebar i t)) (ebar j t)) :
    covariantDerivCoord (I := I') g' α' ubar
        (fun r => covariantDerivCoord (I := I') g' α' ubar (fun s => ∑ i, y i s • ebar i s) r) t
      + chartCurvatureEndo (I := I') g' α' (ubar t) (deriv ubar t) (∑ i, y i t • ebar i t) = 0 := by
  classical
  -- do Carmo: on `M`, `J = Σ yᵢ eᵢ` Jacobi ⟹ the scalar system `yⱼ'' + Σᵢ aᵢⱼ yᵢ = 0`.
  have hscalar : ∀ j, deriv (deriv (y j)) t
      + ∑ i, y i t * chartMetricInner (I := I) g α (u t)
          (chartCurvatureEndo (I := I) g α (u t) (deriv u t) (e i t)) (e j t) = 0 :=
    fun j => frameJacobiComponent (I := I) g α u y e
      (chartCurvatureEndo (I := I) g α (u t) (deriv u t)) hf hf2 he hpar horth hjac j
  -- The curvature-matching hypothesis ⟹ the identical scalar system with `M̃` coefficients.
  have hscalarbar : ∀ j, deriv (deriv (y j)) t
      + ∑ i, y i t * chartMetricInner (I := I') g' α' (ubar t)
          (chartCurvatureEndo (I := I') g' α' (ubar t) (deriv ubar t) (ebar i t)) (ebar j t) = 0 := by
    intro j
    have hsum : (∑ i, y i t * chartMetricInner (I := I') g' α' (ubar t)
          (chartCurvatureEndo (I := I') g' α' (ubar t) (deriv ubar t) (ebar i t)) (ebar j t))
        = ∑ i, y i t * chartMetricInner (I := I) g α (u t)
          (chartCurvatureEndo (I := I) g α (u t) (deriv u t) (e i t)) (e j t) :=
      Finset.sum_congr rfl fun i _ => by rw [hmatch i j]
    rw [hsum]; exact hscalar j
  -- do Carmo: `J̃ = Σ yᵢ ẽᵢ` satisfies the same equation, hence is a Jacobi field on `M̃`.
  rw [covariantDerivCoord2_add_map_frameCombination_expand (I := I') g' α' ubar y ebar
    (chartCurvatureEndo (I := I') g' α' (ubar t) (deriv ubar t))
    hf hf2 hebar hparbar hcardbar horthbar]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [hscalarbar j, zero_smul]

end Riemannian.Jacobi
