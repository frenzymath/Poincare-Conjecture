import PetersenLib.Ch01.AveragedMetric
import PetersenLib.Ch01.BiinvariantAveraging
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral

/-!
# Petersen Ch. 1, Exercise 1.6.26 — averaging over a compact group action

This file carries Exercise 1.6.26 from the finite case (`AveragedMetric.lean`) to the
general **compact** case: a compact Lie group `Γ` acting smoothly on a manifold `M`
preserves some Riemannian metric.  The recipe is Petersen's: take any metric `g₀`
(`exists_riemannianMetric`, a partition of unity) and average its pullbacks against the
Haar probability measure `μ` of `Γ`,

  `g(u, v) = ∫_Γ g₀(Dγ(u), Dγ(v)) dμ(γ)`.

The **well-posed hypotheses.**  For the averaging to even be stated one needs the partial
tangent map `γ ↦ Dγ_p` to vary measurably in `γ`; the correct setting (resolving the
under-hypothesization noted in issue I-0167) is a compact Lie group `Γ` with a **jointly
smooth** action `Φ : Γ × M → M` (`ContMDiff (J.prod I) I ∞ (fun q => q.1 • q.2)`), rather
than merely per-`γ` smoothness plus joint continuity.

The fibrewise averaging (symmetry and positive-definiteness of `(u,v) ↦ ∫_Γ (γ^*g₀)_p(u,v) dμ`)
is supplied by `PetersenLib.CompactAveraging.avgFormFamily`.  This file discharges the two
analytic facts about the action that it needs:

* **(a) regularity** — continuity in `γ` of the fibre form `γ ↦ (γ^*g₀)_p(u,v)`
  (`pullbackAction_continuous`), via `ContMDiffAt.mfderiv`: the `y`-differential of the
  jointly smooth action varies smoothly in `γ` in tangent coordinates, and pairing it with
  the smooth metric `g₀` gives a continuous scalar.  This feeds the integrability and
  positivity hypotheses of `avgFormFamily`.

The invariance step — `Γ` acts by isometries — is fully proved
(`avgMetricCompact_isRiemannianIsometry`): the chain rule `D(γ·)∘D(δ·) = D((γδ)·)` turns the
`δ`-translate of the average into the reindexing `γ ↦ γδ`, which is absorbed by right
invariance of the Haar measure (`integral_mul_right_eq_self`), exactly as in the finite case.

**The single remaining gap** is the `contMDiff` field of the averaged metric: smoothness in
the base point `p` of the section `p ↦ ∫_Γ (γ^*g₀)_p dμ` needs a `C^∞` parametric-integral
theorem for sections of a vector bundle, which Mathlib does not provide
(`Mathlib/Analysis/Calculus/ParametricIntegral.lean` gives only first derivatives).  It is
isolated as a documented `sorry` in `avgMetricCompact` and nowhere else.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Exercise 1.6.26.
-/

open MeasureTheory Bundle TopologicalSpace
open scoped ContDiff Manifold Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {HF : Type*} [TopologicalSpace HF] {J : ModelWithCorners ℝ F HF}
  {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [ChartedSpace HF Γ]
  [IsManifold J ∞ Γ] [LieGroup J ∞ Γ] [MulAction Γ M]

/-! ## Sub-lemma (a): continuity of the fibre form in the group variable -/

/-- **Eng.** From a jointly smooth action, each element acts smoothly on `M`:
`γ · = (·•·) ∘ (γ, ·)`. -/
theorem contMDiff_smul_of_jointly (hΦ : ContMDiff (J.prod I) I ∞ (fun q : Γ × M => q.1 • q.2))
    (γ : Γ) : ContMDiff I I ∞ (fun q : M => γ • q) :=
  hΦ.comp (contMDiff_const.prodMk contMDiff_id)

/-- **Math.** Sub-lemma (a) for Exercise 1.6.26: for a jointly smooth action of the Lie
group `Γ`, the scalar `γ ↦ (γ^*g₀)_p(u,v) = g₀(Dγ_p u, Dγ_p v)` is **continuous** in the
group variable `γ`.

The `y`-differential of the jointly smooth map `(γ, y) ↦ γ • y`, read in tangent
coordinates around `γ₀·p`, is smooth in `γ` (`ContMDiffAt.mfderiv`); pairing it in both slots
against the smooth metric `g₀`, read in the same coordinates, gives the scalar as a composite
of continuous maps.  Its output lives on the *fixed* fibre `T_pM`, so no bundle over `Γ` is
involved — only the internal differential and metric evaluation move with `γ`. -/
theorem pullbackAction_continuous (g₀ : RiemannianMetric I M)
    (hΦ : ContMDiff (J.prod I) I ∞ (fun q : Γ × M => q.1 • q.2))
    (p : M) (u v : TangentSpace I p) :
    Continuous (fun γ : Γ => pullbackForm g₀ (fun q : M => γ • q) p u v) := by
  rw [continuous_iff_continuousAt]
  intro γ₀
  -- The `y`-differential of the action, in tangent coordinates, is smooth in `γ`.
  have hf : ContMDiffAt (J.prod I) I ∞
      (Function.uncurry (fun (γ : Γ) (q : M) => γ • q)) (γ₀, (fun _ : Γ => p) γ₀) :=
    hΦ.contMDiffAt
  have hmn : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by simp
  have h0 := ContMDiffAt.mfderiv (fun (γ : Γ) (q : M) => γ • q) (fun _ : Γ => p)
    hf contMDiffAt_const hmn
  set Ψ := inTangentCoordinates I I (fun _ : Γ => p)
    (fun γ => (fun (γ : Γ) (q : M) => γ • q) γ ((fun _ : Γ => p) γ))
    (fun γ => mfderiv I I ((fun (γ : Γ) (q : M) => γ • q) γ) ((fun _ : Γ => p) γ)) γ₀ with hΨdef
  have hΨcont : ContinuousAt Ψ γ₀ := h0.continuousAt
  -- trivializations: source at the fixed `p`, target at the moving `γ₀ • p`.
  set sT := trivializationAt E (TangentSpace I) p with hsT
  set tT := trivializationAt E (TangentSpace I) (γ₀ • p) with htT
  have hp : p ∈ sT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) p
  have hγ₀p : γ₀ • p ∈ tT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) (γ₀ • p)
  -- the metric `g₀` read in target coordinates around `γ₀ • p`.
  set G : M → (E →L[ℝ] E →L[ℝ] ℝ) := fun y =>
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ) (γ₀ • p) y (γ₀ • p) y (g₀.inner y) with hGdef
  have hGcont : ContinuousAt G (γ₀ • p) :=
    (((contMDiffAt_hom_bundle _).mp g₀.contMDiff.contMDiffAt).2).continuousAt
  have hbaseCont : Continuous (fun γ : Γ => γ • p) :=
    hΦ.continuous.comp (continuous_id.prodMk continuous_const)
  set uu : E := sT.continuousLinearMapAt ℝ p u with huu
  set vv : E := sT.continuousLinearMapAt ℝ p v with hvv
  -- the manifestly continuous target function.
  have htarget : ContinuousAt (fun γ : Γ => G (γ • p) (Ψ γ uu) (Ψ γ vv)) γ₀ := by
    have h1 : ContinuousAt (fun γ : Γ => G (γ • p)) γ₀ :=
      ContinuousAt.comp (g := G) (f := fun γ : Γ => γ • p) (x := γ₀) hGcont
        hbaseCont.continuousAt
    have h2 : ContinuousAt (fun γ : Γ => Ψ γ uu) γ₀ := hΨcont.clm_apply continuousAt_const
    have h3 : ContinuousAt (fun γ : Γ => Ψ γ vv) γ₀ := hΨcont.clm_apply continuousAt_const
    exact (h1.clm_apply h2).clm_apply h3
  refine htarget.congr ?_
  -- On the neighborhood where `γ • p` stays in the target base set, the coordinate
  -- expression equals the pullback form (the `inCoordinates` unfolding).
  filter_upwards [hbaseCont.continuousAt (tT.open_baseSet.mem_nhds hγ₀p)] with γ hγ
  -- `hγ : γ • p ∈ tT.baseSet`; goal: `G (γ•p) (Ψ γ uu) (Ψ γ vv) = pullbackForm g₀ (γ•·) p u v`
  have hγ' : γ • p ∈ tT.baseSet := hγ
  -- read `Ψ γ w` back through the target trivialization to `D(γ·)_p (source coords of w)`
  have hΨval : ∀ w : E, tT.symm (γ • p) (Ψ γ w)
      = mfderiv I I (fun q : M => γ • q) p (sT.symm p w) := by
    intro w
    have hval : Ψ γ w = tT.continuousLinearEquivAt ℝ (γ • p) hγ'
        (mfderiv I I (fun q : M => γ • q) p ((sT.continuousLinearEquivAt ℝ p hp).symm w)) := by
      rw [hΨdef]
      simp only [inTangentCoordinates]
      rw [ContinuousLinearMap.inCoordinates_eq hp hγ']
      rfl
    have hcoeT : (tT.symm (γ • p) : E → TangentSpace I (γ • p))
        = ⇑(tT.continuousLinearEquivAt ℝ (γ • p) hγ').symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq tT hγ']; rfl
    have hcoeS : (sT.symm p : E → TangentSpace I p)
        = ⇑(sT.continuousLinearEquivAt ℝ p hp).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq sT hp]; rfl
    rw [hval, hcoeT, ContinuousLinearEquiv.symm_apply_apply, hcoeS]
  have hsymmU : sT.symm p uu = u := by rw [huu]; exact sT.symmL_continuousLinearMapAt hp u
  have hsymmV : sT.symm p vv = v := by rw [hvv]; exact sT.symmL_continuousLinearMapAt hp v
  -- unfold `G (γ•p)` (metric in target coordinates) via the bilinear `inCoordinates` lemma
  have htrivR : trivializationAt ℝ (Bundle.Trivial M ℝ) (γ₀ • p)
      = Bundle.Trivial.trivialization M ℝ := Bundle.Trivial.eq_trivialization M ℝ _
  rw [hGdef, inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M ℝ) hγ' hγ' (by simp)]
  simp only [htrivR, Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq,
    ← htT, hΨval, hsymmU, hsymmV, pullbackForm_apply, RiemannianMetric.metricInner_apply]

/-! ## The averaged metric over a compact group action -/

section Compact

variable [FiniteDimensional ℝ E] [CompactSpace Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  [MeasurableMul Γ]

/-- Each scalar slice `γ ↦ (γ^*g₀)_p(x,y)` is integrable: continuous on the compact `Γ`
against a finite measure. -/
theorem pullbackAction_integrable (μ : Measure Γ) [IsFiniteMeasure μ]
    (g₀ : RiemannianMetric I M)
    (hΦ : ContMDiff (J.prod I) I ∞ (fun q : Γ × M => q.1 • q.2))
    (p : M) (u v : TangentSpace I p) :
    Integrable (fun γ : Γ => pullbackForm g₀ (fun q : M => γ • q) p u v) μ :=
  (pullbackAction_continuous g₀ hΦ p u v).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

variable (μ : Measure Γ) [IsProbabilityMeasure μ]

/-- **Math.** Petersen Exercise 1.6.26 (compact case): the **averaged metric**
`g(u,v) = ∫_Γ g₀(Dγ(u), Dγ(v)) dμ(γ)` on `M`.  Symmetric and positive-definite fibrewise
(`avgFormFamily`), with `Γ`-invariance proved separately (`avgMetricCompact_preservesMetric`).

The `contMDiff` field is the sole remaining gap: smoothness in `p` of the parametric integral
of the bundle-section `p ↦ ∫_Γ (γ^*g₀)_p dμ` needs a `C^∞` parametric-integral theorem for
sections of a vector bundle that Mathlib lacks (first derivatives only). -/
def avgMetricCompact (g₀ : RiemannianMetric I M)
    (hΦ : ContMDiff (J.prod I) I ∞ (fun q : Γ × M => q.1 • q.2)) :
    RiemannianMetric I M where
  inner p := CompactAveraging.avgFormFamily (V := E) μ
    (fun γ => pullbackForm g₀ (fun q : M => γ • q) p)
    (fun x y => pullbackAction_integrable μ g₀ hΦ p x y)
  symm p u v := CompactAveraging.avgFormFamily_symm (V := E) μ
    (fun x y => pullbackAction_integrable μ g₀ hΦ p x y)
    (fun γ a b => pullbackForm_symm g₀ (fun q : M => γ • q) p a b) u v
  pos p u hu := CompactAveraging.avgFormFamily_pos (V := E) μ
    (fun x y => pullbackAction_integrable μ g₀ hΦ p x y)
    (fun x => pullbackAction_continuous g₀ hΦ p x x)
    (fun γ x hx => pullbackForm_pos g₀ (fun q : M => γ • q) p
      (mfderiv_smul_injective (contMDiff_smul_of_jointly hΦ) γ p) x hx) u hu
  isVonNBounded p := by
    refine isVonNBounded_of_posDef (E := E)
      (CompactAveraging.avgFormFamily (V := E) μ
        (fun γ => pullbackForm g₀ (fun q : M => γ • q) p)
        (fun x y => pullbackAction_integrable μ g₀ hΦ p x y)) (fun u hu => ?_)
    exact CompactAveraging.avgFormFamily_pos (V := E) μ
      (fun x y => pullbackAction_integrable μ g₀ hΦ p x y)
      (fun x => pullbackAction_continuous g₀ hΦ p x x)
      (fun γ x hx => pullbackForm_pos g₀ (fun q : M => γ • q) p
        (mfderiv_smul_injective (contMDiff_smul_of_jointly hΦ) γ p) x hx) u hu
  contMDiff := by
    -- GAP (the sole remaining obstruction to Exercise 1.6.26): smoothness in the base
    -- point `p` of the section `p ↦ ∫_Γ (γ^*g₀)_p dμ`.  In a chart this is a parametric
    -- integral `x ↦ ∫_Γ Φ(γ, x) dμ` of a jointly (in `x`) `C^∞`, continuous-in-`γ`
    -- integrand over the compact `Γ`; concluding it is `C^∞` needs a `C^∞`
    -- parametric-integral theorem for bundle-valued sections, which Mathlib does not
    -- provide (`Mathlib/Analysis/Calculus/ParametricIntegral.lean` has first derivatives
    -- only).  Everything else in this construction is proved sorry-free.
    sorry

@[simp]
theorem avgMetricCompact_apply (g₀ : RiemannianMetric I M)
    (hΦ : ContMDiff (J.prod I) I ∞ (fun q : Γ × M => q.1 • q.2))
    (p : M) (u v : TangentSpace I p) :
    (avgMetricCompact μ g₀ hΦ).metricInner p u v
      = ∫ γ : Γ, g₀.metricInner (γ • p)
          (mfderiv I I (fun q : M => γ • q) p u) (mfderiv I I (fun q : M => γ • q) p v) ∂μ := by
  show CompactAveraging.avgFormFamily (V := E) μ _ _ u v = _
  rw [CompactAveraging.avgFormFamily_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun γ => pullbackForm_apply _ _ _ _ _)

/-! ## `Γ` acts by isometries for the averaged metric -/

variable [μ.IsMulRightInvariant]

/-- **Math.** Petersen Exercise 1.6.26 (invariance step): the averaged metric is
`Γ`-invariant.  By the chain rule `D(γ·)_{δ·p} ∘ D(δ·)_p = D((γδ)·)_p`, the `δ`-translate of
the average is the integral of `γ ↦ g₀((γδ)·p, D(γδ)u, D(γδ)v)`; the reindexing `γ ↦ γδ` is
absorbed by right invariance of the Haar measure (`integral_mul_right_eq_self`). -/
theorem avgMetricCompact_preservesMetric (g₀ : RiemannianMetric I M)
    (hΦ : ContMDiff (J.prod I) I ∞ (fun q : Γ × M => q.1 • q.2)) (δ : Γ) :
    PreservesMetric (avgMetricCompact μ g₀ hΦ) (avgMetricCompact μ g₀ hΦ)
      (fun p : M => δ • p) := by
  intro p u v
  have hs := contMDiff_smul_of_jointly hΦ
  have hδ : MDifferentiableAt I I (fun q : M => δ • q) p := (hs δ p).mdifferentiableAt (by simp)
  -- chain rule, one group element at a time
  have hchain : ∀ γ : Γ, ∀ w : TangentSpace I p,
      mfderiv I I (fun q : M => γ • q) (δ • p) (mfderiv I I (fun q : M => δ • q) p w)
        = mfderiv I I (fun q : M => (γ * δ) • q) p w := by
    intro γ w
    have hγ : MDifferentiableAt I I (fun q : M => γ • q) (δ • p) :=
      (hs γ (δ • p)).mdifferentiableAt (by simp)
    have hcomp : (fun q : M => γ • q) ∘ (fun q : M => δ • q) = fun q : M => (γ * δ) • q := by
      funext q; rw [Function.comp_apply, smul_smul]
    have h := mfderiv_comp (I := I) (I' := I) (I'' := I) p hγ hδ
    rw [hcomp] at h
    exact congrArg (fun L : TangentSpace I p →L[ℝ] TangentSpace I (δ • p) => L w) h.symm
  rw [avgMetricCompact_apply, avgMetricCompact_apply]
  -- rewrite each integrand at `δ • p` into the `γδ`-integrand at `p`
  have hterm : ∀ γ : Γ,
      g₀.metricInner (γ • (δ • p))
          (mfderiv I I (fun q : M => γ • q) (δ • p) (mfderiv I I (fun q : M => δ • q) p u))
          (mfderiv I I (fun q : M => γ • q) (δ • p) (mfderiv I I (fun q : M => δ • q) p v))
        = g₀.metricInner ((γ * δ) • p)
            (mfderiv I I (fun q : M => (γ * δ) • q) p u)
            (mfderiv I I (fun q : M => (γ * δ) • q) p v) := by
    intro γ; rw [hchain γ u, hchain γ v, smul_smul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hterm)]
  exact (integral_mul_right_eq_self
    (fun γ : Γ => g₀.metricInner (γ • p)
      (mfderiv I I (fun q : M => γ • q) p u) (mfderiv I I (fun q : M => γ • q) p v)) δ).symm

/-- **Math.** Petersen Exercise 1.6.26 (compact case): for the averaged metric every element
of `Γ` acts as a **Riemannian isometry** — a diffeomorphism (`actionDiffeomorph`) preserving
the metric (`avgMetricCompact_preservesMetric`). -/
theorem avgMetricCompact_isRiemannianIsometry (g₀ : RiemannianMetric I M)
    (hΦ : ContMDiff (J.prod I) I ∞ (fun q : Γ × M => q.1 • q.2)) (δ : Γ) :
    IsRiemannianIsometry (avgMetricCompact μ g₀ hΦ) (avgMetricCompact μ g₀ hΦ)
      (fun p : M => δ • p) :=
  ⟨⟨actionDiffeomorph I (contMDiff_smul_of_jointly hΦ) δ, rfl⟩,
    avgMetricCompact_preservesMetric μ g₀ hΦ δ⟩

end Compact

/-! ## Exercise 1.6.26 for a compact Lie group -/

/-- **Math.** Petersen Exercise 1.6.26: if a **compact** Lie group `Γ` acts smoothly (jointly)
on a manifold `M`, then `M` carries a Riemannian metric for which `Γ` acts by isometries.

Take any metric `g₀` (`exists_riemannianMetric`, via a partition of unity) and average its
pullbacks against the normalised Haar (probability) measure `μ` of `Γ`, made right invariant
by pushing forward along inversion.  Symmetry, positivity, and invariance of the average are
proved (`avgMetricCompact_isRiemannianIsometry`); the smoothness of the averaged section in
the base point is the sole gap (a `C^∞` parametric-integral theorem for bundle sections, which
Mathlib lacks), isolated as the `contMDiff` field of `avgMetricCompact`. -/
theorem exercise1_6_26 [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [CompactSpace Γ] [T2Space Γ]
    (hΦ : ContMDiff (J.prod I) I ∞ (fun q : Γ × M => q.1 • q.2)) :
    ∃ g : RiemannianMetric I M, ∀ γ : Γ,
      IsRiemannianIsometry g g (fun p : M => γ • p) := by
  haveI : IsTopologicalGroup Γ := topologicalGroup_of_lieGroup (I := J) (n := ∞)
  haveI : Nonempty Γ := ⟨1⟩
  letI : MeasurableSpace Γ := borel Γ
  haveI : BorelSpace Γ := ⟨rfl⟩
  -- normalised Haar (probability) measure, made right-invariant via inversion.
  haveI hprob₀ : IsProbabilityMeasure (Measure.haarMeasure (⊤ : PositiveCompacts Γ)) := by
    refine ⟨?_⟩
    rw [show (Set.univ : Set Γ) = ↑(⊤ : PositiveCompacts Γ) from PositiveCompacts.coe_top.symm]
    exact Measure.haarMeasure_self
  set μ : Measure Γ := (Measure.haarMeasure (⊤ : PositiveCompacts Γ)).inv with hμ
  haveI : μ.IsMulRightInvariant := by rw [hμ]; infer_instance
  haveI : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    rw [hμ, Measure.inv_apply, Set.inv_univ]
    exact hprob₀.measure_univ
  obtain ⟨g₀⟩ := exists_riemannianMetric (I := I) (M := M)
  exact ⟨avgMetricCompact μ g₀ hΦ, fun γ => avgMetricCompact_isRiemannianIsometry μ g₀ hΦ γ⟩

end PetersenLib
