/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Geodesic/FlowHomogeneity.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import PetersenLib.Riemannian.Geodesic.ChartFlow

set_option linter.unusedSectionVars false

/-!
# Fibre–time homogeneity of the coordinate geodesic spray flow

do Carmo Ch. 3, Lemma 2.6 (`γ(t, q, a v) = γ(a t, q, v)`), formulated at the
level of the **coordinate spray flow** in the chart at `p`, with a *free base
point* `y` (not tied to `extChartAt I p p`).

The manifold-level homogeneity lemmas (`maximalGeodesic_fiberScale`,
`IsGeodesicOnWithInitial.fiberScale`) route through a geodesic *witness* whose
foot is a genuine manifold point, and the witness-descent lemma
`isGeodesicOnWithInitial_of_hasDerivAt_sprayCoord` is available only for a
solution anchored at the chart center `extChartAt I p p`. For the *moving-base*
Gauss estimate (`gauss_surface_computation_at`, `Exponential/MovingBaseGauss.lean`)
one needs the same reparametrization identity for the spray flow through a free
base point `y = extChartAt I p q`, and there is **no** manifold descent available
there (that would require the Christoffel data of the chart at `q`). This file
supplies the identity purely at the coordinate/ODE level — no manifold descent —
via Grönwall uniqueness of the coordinate spray ODE:

* `hasDerivAt_sprayCoord_rescale` — the fibre–time rescaling
  `σ ↦ (Zc(a σ)₁, a · Zc(a σ)₂)` of a spray-ODE solution `Zc` is again a
  solution of the spray ODE (the algebraic heart: degree-2 fibre homogeneity
  `geodesicSprayCoord_smul_velocity` compensates the `a`-time rescaling against
  the `a`-fibre rescaling);
* `sprayCoord_eqOn_of_hasDerivAt` — two solutions of the coordinate spray ODE on
  an open interval, valued in a common Lipschitz region and agreeing at an
  interior time, coincide (Grönwall, `ODE_solution_unique_of_mem_Ioo`);
* `sprayCoord_fst_fibre_time` — the resulting **base-point-free** homogeneity of
  the horizontal component: any spray-ODE solution `α` with
  `α 0 = (Zc 0₁, a · Zc 0₂)` has `(α τ)₁ = (Zc (a τ))₁` throughout the window.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

namespace PetersenLib
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The fibre–time rescaling map `S_a` on `E × E`: identity on the
horizontal (base) component, scaling by `a` on the vertical (velocity)
component. -/
def sprayRescale (a : ℝ) : (E × E) →L[ℝ] (E × E) :=
  (ContinuousLinearMap.fst ℝ E E).prod (a • ContinuousLinearMap.snd ℝ E E)

@[simp] lemma sprayRescale_apply (a : ℝ) (z : E × E) :
    sprayRescale (E := E) a z = (z.1, a • z.2) := by
  simp [sprayRescale]

/-- **Math.** **Fibre–time rescaling preserves the coordinate spray ODE.** If
`Zc` solves `z' = F(z)` for the coordinate spray `F = geodesicSprayCoord g p` at
the time `a * t`, then the rescaled curve `σ ↦ (Zc(a σ)₁, a · Zc(a σ)₂)` solves
the same ODE at `t`. The vertical component picks up an extra `a` from the fibre
rescaling and another `a` from the time rescaling; the degree-2 fibre homogeneity
`geodesicSprayCoord_smul_velocity` turns the resulting `a²` into the acceleration
of the `a`-scaled velocity, so the pair is again a spray value. This is the
coordinate form of do Carmo's homogeneity Lemma 2.6. -/
theorem hasDerivAt_sprayCoord_rescale
    (g : RiemannianMetric I M) (p : M) (a : ℝ) {Zc : ℝ → E × E} {t : ℝ}
    (hZc : HasDerivAt Zc
      (geodesicSprayCoord (I := I) g p (Zc (a * t)).1 (Zc (a * t)).2) (a * t)) :
    HasDerivAt (fun σ : ℝ => ((Zc (a * σ)).1, a • (Zc (a * σ)).2))
      (geodesicSprayCoord (I := I) g p (Zc (a * t)).1 (a • (Zc (a * t)).2)) t := by
  -- reparametrize time by `a`
  have hlin : HasDerivAt (fun σ : ℝ => a * σ) a t := by
    simpa using (hasDerivAt_id t).const_mul a
  have hcomp : HasDerivAt (fun σ : ℝ => Zc (a * σ))
      (a • geodesicSprayCoord (I := I) g p (Zc (a * t)).1 (Zc (a * t)).2) t :=
    hZc.scomp t hlin
  -- apply the linear rescaling `S_a`
  have hSd : HasDerivAt (fun σ : ℝ => sprayRescale (E := E) a (Zc (a * σ)))
      (sprayRescale (E := E) a
        (a • geodesicSprayCoord (I := I) g p (Zc (a * t)).1 (Zc (a * t)).2)) t :=
    (sprayRescale (E := E) a).hasFDerivAt.comp_hasDerivAt t hcomp
  have hfun : (fun σ : ℝ => sprayRescale (E := E) a (Zc (a * σ)))
      = (fun σ : ℝ => ((Zc (a * σ)).1, a • (Zc (a * σ)).2)) := by
    funext σ; rw [sprayRescale_apply]
  rw [hfun] at hSd
  refine hSd.congr_deriv ?_
  rw [sprayRescale_apply, geodesicSprayCoord_smul_velocity]
  refine Prod.ext ?_ ?_
  · simp [geodesicSprayCoord_def]
  · simp [smul_smul]

/-- **Math.** **Grönwall uniqueness for the coordinate spray ODE.** Two solutions
`α, β` of `z' = geodesicSprayCoord g p z` on an open interval `Ioo a b`, both
valued in a set `s` on which the coordinate spray is `K`-Lipschitz, that agree at
one interior time `t₀`, coincide on all of `Ioo a b`. -/
theorem sprayCoord_eqOn_of_hasDerivAt
    (g : RiemannianMetric I M) (p : M) {s : Set (E × E)} {K : ℝ≥0}
    (hlip : LipschitzOnWith K
      (fun z : E × E => geodesicSprayCoord (I := I) g p z.1 z.2) s)
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) {α β : ℝ → E × E}
    (hα : ∀ t ∈ Ioo a b,
      HasDerivAt α (geodesicSprayCoord (I := I) g p (α t).1 (α t).2) t ∧ α t ∈ s)
    (hβ : ∀ t ∈ Ioo a b,
      HasDerivAt β (geodesicSprayCoord (I := I) g p (β t).1 (β t).2) t ∧ β t ∈ s)
    (h0 : α t₀ = β t₀) :
    EqOn α β (Ioo a b) :=
  ODE_solution_unique_of_mem_Ioo
    (v := fun _ z => geodesicSprayCoord (I := I) g p z.1 z.2) (s := fun _ => s)
    (fun _ _ => hlip) ht₀ hα hβ h0

/-- **Math.** **Base-point-free fibre–time homogeneity of the spray flow.** Let
`Zc` be a coordinate spray-ODE solution whose values at the rescaled times
`a · τ` (for `τ` in an open window `Ioo c d ∋ 0`) satisfy the ODE, and let `α` be
a spray-ODE solution on the same window with `α 0 = (Zc 0₁, a · Zc 0₂)`. If both
`α` and the rescaled curve stay in a common Lipschitz region `s`, then the
horizontal component of `α` is the `a`-time-reparametrized horizontal component
of `Zc`:

`(α τ)₁ = (Zc (a τ))₁`   for all `τ ∈ Ioo c d`.

At `a = t`, `τ = 1`, this is do Carmo's `exp_q(t v) = exp_q(v)|_{t}` read in the
fixed chart at `p`, with `q` an arbitrary base point. -/
theorem sprayCoord_fst_fibre_time
    (g : RiemannianMetric I M) (p : M) (a : ℝ) {s : Set (E × E)} {K : ℝ≥0}
    (hlip : LipschitzOnWith K
      (fun z : E × E => geodesicSprayCoord (I := I) g p z.1 z.2) s)
    {c d : ℝ} (hc : c < 0) (hd : 0 < d)
    {α Zc : ℝ → E × E}
    (hα : ∀ τ ∈ Ioo c d,
      HasDerivAt α (geodesicSprayCoord (I := I) g p (α τ).1 (α τ).2) τ ∧ α τ ∈ s)
    (hZc : ∀ τ ∈ Ioo c d,
      HasDerivAt Zc
        (geodesicSprayCoord (I := I) g p (Zc (a * τ)).1 (Zc (a * τ)).2) (a * τ))
    (hζmem : ∀ τ ∈ Ioo c d, ((Zc (a * τ)).1, a • (Zc (a * τ)).2) ∈ s)
    (h0 : α 0 = ((Zc 0).1, a • (Zc 0).2))
    {τ : ℝ} (hτ : τ ∈ Ioo c d) :
    (α τ).1 = (Zc (a * τ)).1 := by
  set ζ : ℝ → E × E := fun σ : ℝ => ((Zc (a * σ)).1, a • (Zc (a * σ)).2) with hζdef
  have h0mem : (0 : ℝ) ∈ Ioo c d := ⟨hc, hd⟩
  have hζ : ∀ σ ∈ Ioo c d,
      HasDerivAt ζ (geodesicSprayCoord (I := I) g p (ζ σ).1 (ζ σ).2) σ ∧ ζ σ ∈ s := by
    intro σ hσ
    refine ⟨?_, hζmem σ hσ⟩
    exact hasDerivAt_sprayCoord_rescale (I := I) g p a (hZc σ hσ)
  have heqOn : EqOn α ζ (Ioo c d) :=
    sprayCoord_eqOn_of_hasDerivAt (I := I) g p hlip h0mem hα hζ
      (by rw [h0]; simp [hζdef, mul_zero])
  have := heqOn hτ
  rw [this]

end Geodesic
end PetersenLib
