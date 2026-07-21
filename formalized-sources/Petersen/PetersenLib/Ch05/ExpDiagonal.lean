import PetersenLib.Ch05.ExponentialMap
import PetersenLib.Riemannian.Exponential.TotallyNormalCInfty

/-!
# Petersen Ch. 5, §5.5.1 — Prop. 5.5.1 (2): `E(v) = (π v, exp v)` near the diagonal

Blueprint node `prop:pet-ch5-exp-diffeomorphism-properties`, part (2).  Part (1)
(`expMap_localDiffeomorphism`, `Ch05/ExponentialMap.lean`) says `D exp_p` is the
identity at `0 ∈ T_pM`.  Part (2) is about the map

  `E : O → M × M`,  `E(v) = (π v, exp v)`

on a neighbourhood `O` of the zero section of `TM`: its differential at `0_p` is
nonsingular (in coordinates `(q, v) ↦ (q, exp_q v)` it is the unipotent shear
`[[I, 0], [I, I]]`), so by the inverse function theorem `E` is a diffeomorphism
from a neighbourhood of the zero section onto a neighbourhood of the diagonal in
`M × M`.

`expDiagonalMap_localDiffeomorphism` below is the **chart-level** form of that
statement, in the same idiom as `expMap_localDiffeomorphism`: everything is read
through the extended chart `φ_p` at `p`, and `E` appears as its chart reading

  `Ê(y, w) = (y, (Z (y, T⁻¹ • w) T).1)`,

where `Z` is a local flow of the chart-`p` geodesic spray and `T` a Picard time.
The clause `hgeo` is what makes this the honest reading of `E`: for every base
`q ∈ W` and every chart velocity `‖w‖ < δ` it exhibits an honest *intrinsic*
geodesic `γ` on `[0, 1]` with `γ 0 = q` and chart-`p` initial velocity `w`, and
identifies `Ê(φ_p q, w) = (φ_p q, φ_p (γ 1))`.  Thus `Ê`'s second component is
`φ_p(exp_q v)` for the velocity `v ∈ T_qM` whose chart-`p` coordinate is `w`.

The regularity is `C^∞`, matching Petersen's claim: it comes from the vendored
`Exponential.exists_totallyNormal_cinfty_diffeo`, whose engine is the `C^∞`
initial-condition dependence of the geodesic flow
(`Geodesic.exists_uniform_geodesic_flow_contDiffAt`).  Note that no joint
smoothness in `(q, v, t)` is needed anywhere: `E` evaluates the flow at the
*fixed* time `T`, so time never enters as a variable.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

open PetersenLib.Geodesic PetersenLib.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] [T2Space M]

/-- **Math.** Petersen Ch. 5 (`prop:pet-ch5-exp-diffeomorphism-properties`, Prop.
5.5.1 (2)): **`E(v) = (π v, exp v)` is a local diffeomorphism from a neighbourhood
of the zero section of `TM` onto a neighbourhood of the diagonal of `M × M`**, in
its chart reading at `p`.

For every `p ∈ M` there are an open `W ∋ p` inside the chart at `p`, radii
`δ, δ₁ > 0`, a Picard time `T > 0`, a local flow `Z` of the chart-`p` geodesic
spray and a map `Einv` such that, writing

  `Ê(y, w) = (y, (Z (y, T⁻¹ • w) T).1)`   and   `Ω = B_{δ₁}(φ_p p) ×ˢ B_δ(0)`

for the chart reading of `E` and for the chart reading of a neighbourhood of the
zero section:

* **(zero section)** `φ_p(W) ⊆ B_{δ₁}(φ_p p)`, so `(φ_p q, 0) ∈ Ω` for all
  `q ∈ W`: `Ω` really is a chart neighbourhood of the piece of the zero section
  over `W` (in particular `Ω ≠ ∅`, and the package is not vacuous);
* **(`Ê` is the chart reading of `E`)** for every `q ∈ W` and `‖w‖ < δ` there is
  an intrinsic geodesic `γ` on `[0, 1]` with `γ 0 = q`, chart-`p` initial velocity
  `w`, staying in the chart at `p`, and `Ê(φ_p q, w) = (φ_p q, φ_p (γ 1))` — i.e.
  the second component of `Ê` is `φ_p(exp_q v)` for the velocity `v ∈ T_qM` with
  chart-`p` coordinate `w`;
* **(nonsingular differential at `0_p`)** `Ê` is strictly differentiable at
  `(φ_p p, 0)` with derivative the unipotent shear `(a, b) ↦ (a, a + b)`, i.e.
  Petersen's `[[I, 0], [I, I]]`, a linear *equivalence*;
* **(local diffeomorphism)** `Ê` is `C^∞` and injective on `Ω`, its image `Ê(Ω)`
  is open, `Einv` is a two-sided inverse of `Ê` between `Ω` and `Ê(Ω)`, and `Einv`
  is `C^∞` on `Ê(Ω)`;
* **(the image is a neighbourhood of the diagonal of `W`)** `(φ_p q, φ_p m) ∈ Ê(Ω)`
  for *all* `q, m ∈ W` — in particular `Ê(Ω)` contains the chart reading of the
  whole diagonal `{(q, q) : q ∈ W}`.

This is the vendored `Exponential.exists_totallyNormal_cinfty_diffeo` (do Carmo's
Theorem 3.7 at `C^∞` regularity) read as Petersen's Prop. 5.5.1 (2), together with
the shear derivative of
`Exponential.exists_pairMap_hasStrictFDerivAt_equiv_ball_infty`. -/
theorem expDiagonalMap_localDiffeomorphism (g : RiemannianMetric I M) (p : M) :
    ∃ (W : Set M) (δ δ₁ T : ℝ) (Z : E × E → ℝ → E × E) (Einv : E × E → E × E),
      IsOpen W ∧ p ∈ W ∧ W ⊆ (chartAt H p).source ∧
      0 < δ ∧ 0 < δ₁ ∧ 0 < T ∧
      -- the chart reading of a neighbourhood of the zero section over `W`
      (∀ q ∈ W, ((extChartAt I p q, (0 : E)) : E × E) ∈
        ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ) ∧
      -- `Ê` is the chart reading of `E(v) = (π v, exp v)`
      (∀ q ∈ W, ∀ w : E, ‖w‖ < δ →
        ∃ γ : ℝ → M,
          γ 0 = q ∧
          ContinuousOn γ (Icc 0 1) ∧
          IsGeodesicOn (I := I) g γ (Icc 0 1) ∧
          (∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ (chartAt H p).source) ∧
          HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0 ∧
          ((extChartAt I p q : E),
              (Z ((extChartAt I p q, T⁻¹ • w) : E × E) T).1) =
            ((extChartAt I p q : E), extChartAt I p (γ 1))) ∧
      -- the differential at the zero vector `0_p` is Petersen's `[[I, 0], [I, I]]`
      HasStrictFDerivAt
        (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
        ((ContinuousLinearMap.fst ℝ E E).prod
          ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)))
        ((extChartAt I p p, (0 : E)) : E × E) ∧
      -- `Ê` is a `C^∞` diffeomorphism of `Ω` onto an open set
      ContDiffOn ℝ ∞
        (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
        (ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ) ∧
      Set.InjOn
        (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
        (ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ) ∧
      IsOpen ((fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
        '' (ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ)) ∧
      (∀ x ∈ ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ,
        Einv ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1) = x) ∧
      (∀ z ∈ (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
          '' (ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ),
        (((Einv z).1 : E), (Z (((Einv z).1, T⁻¹ • (Einv z).2) : E × E) T).1) = z) ∧
      ContDiffOn ℝ ∞ Einv
        ((fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
          '' (ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ)) ∧
      -- the image contains the chart reading of the diagonal of `W`
      (∀ q ∈ W, ∀ m ∈ W,
        ((extChartAt I p q, extChartAt I p m) : E × E) ∈
          (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
            '' (ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ)) := by
  classical
  obtain ⟨W, δ, δ₁, T, Z, Ginv, hWopen, hpW, hWsub, hδ, hδ₁, hT, hWchart, hshear,
    hnormal, -, hGCinf, hGinj, hGopen, hGinvG, hGGinv, hGinvCinf, hrange⟩ :=
    Exponential.exists_totallyNormal_cinfty_diffeo (I := I) g p
  refine ⟨W, δ, δ₁, T, Z, Ginv, hWopen, hpW, hWsub, hδ, hδ₁, hT, ?_, ?_, hshear,
    hGCinf, hGinj, hGopen, hGinvG, hGGinv, hGinvCinf, hrange⟩
  · -- the chart reading of the zero section over `W` lies in `Ω`
    intro q hq
    exact ⟨hWchart q hq, mem_ball_self hδ⟩
  · -- `Ê` is the chart reading of `E(v) = (π v, exp v)`
    intro q hq w hw
    obtain ⟨γ, hγform, hγ0, hγcont, hγgeo, hγchart, hγvel⟩ := hnormal q hq w hw
    have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    refine ⟨γ, hγ0, hγcont, hγgeo, fun s hs => (hγchart s hs).1, hγvel, ?_⟩
    have h := (hγchart 1 h1).2
    rw [one_mul] at h
    rw [h]

end PetersenLib

end
