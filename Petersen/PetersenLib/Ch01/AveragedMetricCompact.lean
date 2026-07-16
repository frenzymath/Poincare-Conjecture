import PetersenLib.Ch01.AveragedMetric
import PetersenLib.Ch01.BiinvariantAveraging
import PetersenLib.Foundations.ManifoldParametricIntegral
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

**The `contMDiff` field** of the averaged metric — smoothness in the base point `p` of the
section `p ↦ ∫_Γ (γ^*g₀)_p dμ` — is now fully discharged (run 0116, `sorry`-free).  Its
**geometric core** is the joint (in `(γ,p)`) `C^∞`-smoothness of the coordinate action
(`pullbackForm_joint_contMDiffAt` (Step A), `coordAction`/`coordAction_contMDiffOn` (Step B)).
The **analytic assembly** is *scalar-componentwise*: the natural `E →L[ℝ] E →L[ℝ] ℝ`
(CLM-valued) parametric integral cannot be used directly because the two-level operator space has
no synthesising `ContinuousENorm` instance, so `Integrable (fun γ => coordAction …)` is unstatable
(the "2-level-CLM diamond").  Instead, `contMDiffAt_hom_bundle` + `contMDiffOn_bilin_of_apply`
(finite-dimensional reduction) reduce smoothness of `p ↦ inCoordinates_{p₀}(inner p)` to that of
the finitely many SCALAR entries `p ↦ ∫_Γ (coordAction g₀ p₀ γ p) v w dμ` (`coordAction_pairing`,
`inCoordinatesBilin_pairing`), each a genuine `ℝ`-valued Haar average whose `C^∞`-dependence on
`p` is the project-local **manifold parametric-integral engine** `contMDiffOn_integral_scalar`
(`PetersenLib.Foundations.ManifoldParametricIntegral`).

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

/-! ## Sub-lemma (b): joint `C^∞` smoothness of the coordinate action

The geometric core needed for the `contMDiff` field of `avgMetricCompact` (Ex 1.6.26): the
**joint** (in `(γ, p)`) `C^∞` smoothness of the pullback section, transported into the fixed
trivialisation at a reference point `p₀`.  These are the joint (parameter `Γ × M`) generalisations
of `pullbackForm_contMDiffAt`, and are exactly the `hdiff`/joint-continuity inputs the parametric
integral engine requires (see the `contMDiff` gap note below). -/

/-- **Step A.** The joint pullback section `(γ, p) ↦ ⟨p, (γ^*g₀)_p⟩` of the bundle of bilinear
forms is `C^∞` on `Γ × M`.  Joint generalisation of `pullbackForm_contMDiffAt`: differentiate the
jointly smooth action `(γ, y) ↦ γ • y` in the `y`-slot at the moving base point via
`ContMDiffAt.mfderiv` (reference map `g = snd`, so the source reference is the current base point,
matching `contMDiffAt_hom_bundle`), then pair against the smooth metric `g₀` read in coordinates. -/
theorem pullbackForm_joint_contMDiffAt (g₀ : RiemannianMetric I M)
    (hΦ : ContMDiff (J.prod I) I ∞ (fun q : Γ × M => q.1 • q.2))
    (q₀ : Γ × M) :
    ContMDiffAt (J.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : Γ × M => (⟨q.2, pullbackForm g₀ (fun y : M => q.1 • y) q.2⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) q₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_snd, ?_⟩
  set sT := trivializationAt E (TangentSpace I) q₀.2 with hsT
  set tT := trivializationAt E (TangentSpace I) (q₀.1 • q₀.2) with htT
  have hx₀ : q₀.2 ∈ sT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) q₀.2
  have hfx₀ : q₀.1 • q₀.2 ∈ tT.baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) (q₀.1 • q₀.2)
  -- the uncurried action `((γ,p), y) ↦ γ • y` is jointly smooth
  have huncurry : ContMDiffAt ((J.prod I).prod I) I ∞
      (Function.uncurry (fun q : Γ × M => fun y : M => q.1 • y)) (q₀, q₀.2) := by
    have heq : (Function.uncurry (fun q : Γ × M => fun y : M => q.1 • y))
        = (fun q : Γ × M => q.1 • q.2) ∘ (fun p : (Γ × M) × M => (p.1.1, p.2)) := by
      funext p; rfl
    rw [heq]
    exact hΦ.contMDiffAt.comp (q₀, q₀.2) (contMDiffAt_fst.fst.prodMk contMDiffAt_snd)
  have hmn : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by simp
  set D : (Γ × M) → (E →L[ℝ] E) :=
    inTangentCoordinates I I (fun q : Γ × M => q.2) (fun q : Γ × M => q.1 • q.2)
      (fun q : Γ × M => mfderiv I I (fun y : M => q.1 • y) q.2) q₀ with hD
  have hDsmooth : ContMDiffAt (J.prod I) 𝓘(ℝ, E →L[ℝ] E) ∞ D q₀ :=
    ContMDiffAt.mfderiv (fun q : Γ × M => fun y : M => q.1 • y) (fun q : Γ × M => q.2)
      huncurry contMDiffAt_snd hmn
  set G : M → (E →L[ℝ] E →L[ℝ] ℝ) := fun y =>
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ) (q₀.1 • q₀.2) y (q₀.1 • q₀.2) y (g₀.inner y) with hG
  have hGsmooth : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ G (q₀.1 • q₀.2) :=
    ((contMDiffAt_hom_bundle _).mp g₀.contMDiff.contMDiffAt).2
  have hΨ : ContMDiffAt (J.prod I) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun q : Γ × M => ((D q).precomp ℝ).comp ((G (q.1 • q.2)).comp (D q))) q₀ := by
    have h1 : ContMDiffAt (J.prod I) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
        (fun q : Γ × M => (G (q.1 • q.2)).comp (D q)) q₀ :=
      (hGsmooth.comp q₀ hΦ.contMDiffAt).clm_comp hDsmooth
    exact (ContMDiffAt.clm_precomp (F₃ := ℝ) hDsmooth).clm_comp h1
  refine hΨ.congr_of_eventuallyEq ?_
  have hUs : {q : Γ × M | q.2 ∈ sT.baseSet} ∈ 𝓝 q₀ :=
    continuous_snd.continuousAt (sT.open_baseSet.mem_nhds hx₀)
  have hUt : {q : Γ × M | q.1 • q.2 ∈ tT.baseSet} ∈ 𝓝 q₀ :=
    hΦ.continuous.continuousAt (tT.open_baseSet.mem_nhds hfx₀)
  filter_upwards [hUs, hUt] with q hx hfx
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
  have hRHS : (((ContinuousLinearMap.precomp ℝ (D q)).comp ((G (q.1 • q.2)).comp (D q))) a) b
      = G (q.1 • q.2) (D q a) (D q b) := rfl
  have hkey : ∀ u : E, tT.symm (q.1 • q.2) (D q u)
      = mfderiv I I (fun y : M => q.1 • y) q.2 (sT.symm q.2 u) := by
    intro u
    have hDu : D q u = tT.continuousLinearEquivAt ℝ (q.1 • q.2) hfx
        (mfderiv I I (fun y : M => q.1 • y) q.2 ((sT.continuousLinearEquivAt ℝ q.2 hx).symm u)) := by
      rw [hD]
      simp only [inTangentCoordinates]
      rw [ContinuousLinearMap.inCoordinates_eq hx hfx]
      rfl
    have hcoeT : (tT.symm (q.1 • q.2) : E → TangentSpace I (q.1 • q.2))
        = ⇑(tT.continuousLinearEquivAt ℝ (q.1 • q.2) hfx).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq tT hfx]; rfl
    have hcoeS : (sT.symm q.2 : E → TangentSpace I q.2)
        = ⇑(sT.continuousLinearEquivAt ℝ q.2 hx).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq sT hx]; rfl
    rw [hDu, hcoeT, ContinuousLinearEquiv.symm_apply_apply, hcoeS]
  rw [hRHS, hG]
  have htrivM' : trivializationAt ℝ (Bundle.Trivial M ℝ) (q₀.1 • q₀.2)
      = Bundle.Trivial.trivialization M ℝ := Bundle.Trivial.eq_trivialization M ℝ _
  have htrivM : trivializationAt ℝ (Bundle.Trivial M ℝ) q₀.2
      = Bundle.Trivial.trivialization M ℝ := Bundle.Trivial.eq_trivialization M ℝ _
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M ℝ) hfx hfx (by simp)]
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M ℝ) hx hx (by simp)]
  simp only [htrivM', htrivM, Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq,
    pullbackForm_apply, RiemannianMetric.metricInner_apply, ← htT, ← hsT, hkey]

/-- The **coordinate action**: the fixed-reference (`p₀`) coordinate representation of the
pullback form `(γ^*g₀)_p`, valued in the fixed model space `E →L[ℝ] E →L[ℝ] ℝ`.  Naming this map
pins its type, so scalar averages `∫_Γ (coordAction g₀ p₀ γ p) v w dμ` are unambiguous. -/
def coordAction (g₀ : RiemannianMetric I M) (p₀ : M) (γ : Γ) (p : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
    (fun b => TangentSpace I b →L[ℝ] ℝ) p₀ p p₀ p (pullbackForm g₀ (fun q : M => γ • q) p)

/-- **Step B.** Fixed-reference coordinate action.  For a fixed base point `p₀`, the coordinate
representation `(γ, p) ↦ inCoordinates_{p₀}((γ^*g₀)_p)` (`coordAction`) of the joint pullback
section in the trivialisation at `p₀` is jointly `C^∞` on `univ × (baseSet at p₀)`.  Obtained from
Step A via the general `Trivialization.contMDiffOn_iff` (`(e ·).2 = inCoordinates` by
`hom_trivializationAt_apply`) — no manual coordinate change. -/
theorem coordAction_contMDiffOn (g₀ : RiemannianMetric I M)
    (hΦ : ContMDiff (J.prod I) I ∞ (fun q : Γ × M => q.1 • q.2)) (p₀ : M) :
    ContMDiffOn (J.prod I) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun q : Γ × M => coordAction g₀ p₀ q.1 q.2)
      (Set.univ ×ˢ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p₀).baseSet) := by
  have hΦsec : ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : Γ × M => (⟨q.2, pullbackForm g₀ (fun y : M => q.1 • y) q.2⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) :=
    fun q => pullbackForm_joint_contMDiffAt g₀ hΦ q
  have hmaps : Set.MapsTo
      (fun q : Γ × M => (⟨q.2, pullbackForm g₀ (fun y : M => q.1 • y) q.2⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Set.univ ×ˢ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p₀).baseSet)
      (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p₀).source := by
    intro q hq
    rw [Trivialization.mem_source]
    exact hq.2
  have key := (((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p₀).contMDiffOn_iff
      hmaps).mp hΦsec.contMDiffOn).2
  exact key

/-- The fixed-reference coordinate action `γ ↦ coordAction g₀ p₀ γ p` is **continuous** in the
group variable (restriction of Step B to the fibre `γ ↦ (γ, p)`). -/
theorem coordAction_continuous (g₀ : RiemannianMetric I M)
    (hΦ : ContMDiff (J.prod I) I ∞ (fun q : Γ × M => q.1 • q.2)) (p₀ p : M)
    (hp : p ∈ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p₀).baseSet) :
    Continuous (fun γ : Γ => coordAction g₀ p₀ γ p) := by
  have hB := coordAction_contMDiffOn g₀ hΦ p₀
  have hι : ContMDiff J (J.prod I) ∞ (fun γ : Γ => (γ, p)) := contMDiff_id.prodMk contMDiff_const
  have hmaps : Set.MapsTo (fun γ : Γ => (γ, p)) Set.univ
      (Set.univ ×ˢ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p₀).baseSet) :=
    fun γ _ => ⟨Set.mem_univ _, hp⟩
  have hcomp := hB.comp hι.contMDiffOn hmaps
  rw [contMDiffOn_univ] at hcomp
  exact hcomp.continuous

/-- **Joint smoothness of a scalar coordinate entry.**  Post-composing the jointly `C^∞`
coordinate action (`coordAction_contMDiffOn`) with the fixed evaluation `L ↦ L v w` — two
`ContMDiffOn.clm_apply`s against constant sections — the scalar entry
`(γ, p) ↦ coordAction g₀ p₀ γ p v w` is jointly `C^∞` on `univ ×ˢ (baseSet at p₀)`.  This
`ℝ`-valued joint section is the common source of both the `hdiff` (fix `γ`) and `hcont` (joint
continuity of the `p`-derivative) hypotheses that the *scalar* `contDiffOn_parametricIntegral`
requires in the `contMDiff` assembly. -/
theorem coordAction_apply_contMDiffOn (g₀ : RiemannianMetric I M)
    (hΦ : ContMDiff (J.prod I) I ∞ (fun q : Γ × M => q.1 • q.2)) (p₀ : M) (v w : E) :
    ContMDiffOn (J.prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : Γ × M => coordAction g₀ p₀ q.1 q.2 v w)
      (Set.univ ×ˢ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p₀).baseSet) :=
  ((coordAction_contMDiffOn g₀ hΦ p₀).clm_apply contMDiffOn_const).clm_apply contMDiffOn_const

/-- **Scalar coordinate action, paired against fixed model vectors `v w`.**  The pointwise identity
`coordAction g₀ p₀ γ p v w = (γ^*g₀)_p (σ v) (σ w)` with `σ = (trivAt p₀).symm p` the fixed
coordinate map.  This is the key that turns the `E →L[ℝ] E →L[ℝ] ℝ`-valued Bochner average (blocked
by the 2-level-CLM `ContinuousENorm` diamond, see the `contMDiff` gap note) into finitely many
*scalar* averages `∫_Γ (γ^*g₀)_p (σ v) (σ w) dμ`, the entry point to the scalar-componentwise
assembly. -/
theorem coordAction_pairing (g₀ : RiemannianMetric I M) (p₀ p : M)
    (hpE : p ∈ (trivializationAt E (TangentSpace I) p₀).baseSet) (γ : Γ) (v w : E) :
    coordAction g₀ p₀ γ p v w
      = pullbackForm g₀ (fun q : M => γ • q) p
          ((trivializationAt E (TangentSpace I) p₀).symm p v)
          ((trivializationAt E (TangentSpace I) p₀).symm p w) := by
  rw [coordAction, inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M ℝ) hpE hpE (by simp)]
  have htrivM : trivializationAt ℝ (Bundle.Trivial M ℝ) p₀ = Bundle.Trivial.trivialization M ℝ :=
    Bundle.Trivial.eq_trivialization M ℝ _
  simp only [htrivM, Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq]

/-- **Generic fixed-reference `inCoordinates` pairing.**  For any fibre bilinear form `B` on
`T_pM`, its coordinate representation in the trivialisation at `p₀`, paired against model vectors
`v w`, is `B (σ v) (σ w)` with `σ = (trivAt p₀).symm p`.  The form-agnostic core shared by
`coordAction_pairing` (for `B = (γ^*g₀)_p`) and the averaged-section identity below (for
`B = ∫_Γ (γ^*g₀)_p dμ`); it lets a *scalar* coordinate entry commute with the Bochner average. -/
theorem inCoordinatesBilin_pairing (p₀ p : M)
    (hpE : p ∈ (trivializationAt E (TangentSpace I) p₀).baseSet)
    (B : TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) (v w : E) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
        (fun b => TangentSpace I b →L[ℝ] ℝ) p₀ p p₀ p B v w
      = B ((trivializationAt E (TangentSpace I) p₀).symm p v)
          ((trivializationAt E (TangentSpace I) p₀).symm p w) := by
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M ℝ) hpE hpE (by simp)]
  have htrivM : trivializationAt ℝ (Bundle.Trivial M ℝ) p₀ = Bundle.Trivial.trivialization M ℝ :=
    Bundle.Trivial.eq_trivialization M ℝ _
  simp only [htrivM, Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq]

/-! ## The averaged metric over a compact group action -/

section Compact

variable [FiniteDimensional ℝ E] [CompactSpace Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  [MeasurableMul Γ] [SecondCountableTopology Γ] [I.Boundaryless] [J.Boundaryless]

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

The `contMDiff` field — smoothness in `p` of the section `p ↦ ∫_Γ (γ^*g₀)_p dμ` — is fully
discharged (run 0116): after `contMDiffAt_hom_bundle` and the finite-dimensional scalar reduction
`contMDiffOn_bilin_of_apply`, each coordinate entry is the SCALAR Haar average
`p ↦ ∫_Γ (coordAction g₀ p₀ γ p) v w dμ`, whose smoothness in `p` is the project-local manifold
parametric-integral engine `contMDiffOn_integral_scalar`.  Working entirely with `ℝ`-valued
integrals sidesteps the two-level operator `ContinuousENorm` gap (a `E →L[ℝ] E →L[ℝ] ℝ`-valued
Bochner integral is unstatable). -/
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
    -- === RESOLVED (run 0116 s0006): the scalar-componentwise assembly is now complete. ===
    -- Descend to the base chart at `p₀`, reduce the fibre form to its scalar coordinate entries
    -- (`contMDiffOn_bilin_of_apply`, `E` finite-dimensional), and recognise each entry as the
    -- SCALAR Haar average of the coordinate action, whose smoothness in `p` is supplied by the
    -- manifold parametric-integral engine `contMDiffOn_integral_scalar`
    -- (`PetersenLib.Foundations.ManifoldParametricIntegral`).  Only `ℝ`-valued integrals ever
    -- appear, so the two-level operator `ContinuousENorm` diamond is never touched.
    intro p₀
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    set U := (trivializationAt E (TangentSpace I) p₀).baseSet ∩
      (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p₀).baseSet with hU
    have hUopen : IsOpen U :=
      (Trivialization.open_baseSet _).inter (Trivialization.open_baseSet _)
    have hp₀U : p₀ ∈ U :=
      ⟨mem_baseSet_trivializationAt _ _ _, mem_baseSet_trivializationAt _ _ _⟩
    refine ContMDiffOn.contMDiffAt ?_ (hUopen.mem_nhds hp₀U)
    refine contMDiffOn_bilin_of_apply hUopen (fun v w => ?_)
    refine (contMDiffOn_integral_scalar (J := J) (I := I) (μ := μ)
      (f := fun γ p => coordAction g₀ p₀ γ p v w) hUopen ?_).congr (fun p hp => ?_)
    · exact (coordAction_apply_contMDiffOn g₀ hΦ p₀ v w).mono
        (fun q hq => ⟨hq.1, hq.2.2⟩)
    · rw [inCoordinatesBilin_pairing p₀ p hp.1 _ v w]
      show CompactAveraging.avgFormFamily (V := E) μ _ _ _ _ = _
      rw [CompactAveraging.avgFormFamily_apply]
      exact integral_congr_ae (Filter.Eventually.of_forall fun γ =>
        (coordAction_pairing g₀ p₀ p hp.1 γ v w).symm)

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

/-- **Entry point to the scalar-componentwise assembly of `avgMetricCompact.contMDiff`.**  The
`(v, w)`-scalar entry of the fixed-`p₀` coordinate representation of the averaged fibre form
`inner p = ∫_Γ (γ^*g₀)_p dμ` equals the *scalar* Bochner average of the coordinate action:
`inCoordinates_{p₀}(inner p) v w = ∫_Γ coordAction g₀ p₀ γ p v w dμ`.  This is precisely the
identity that dodges the 2-level-CLM `ContinuousENorm` diamond — the `E →L[ℝ] E →L[ℝ] ℝ`-valued
average need never be integrated; only these finitely many scalar integrals do, each a genuine
`ℝ`-valued parametric integral whose smoothness in `p` `contDiffOn_parametricIntegral` supplies. -/
theorem avgMetricCompact_inCoordinates_pairing (g₀ : RiemannianMetric I M)
    (hΦ : ContMDiff (J.prod I) I ∞ (fun q : Γ × M => q.1 • q.2)) (p₀ p : M)
    (hpE : p ∈ (trivializationAt E (TangentSpace I) p₀).baseSet) (v w : E) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
        (fun b => TangentSpace I b →L[ℝ] ℝ) p₀ p p₀ p
        ((avgMetricCompact μ g₀ hΦ).inner p) v w
      = ∫ γ : Γ, coordAction g₀ p₀ γ p v w ∂μ := by
  rw [inCoordinatesBilin_pairing p₀ p hpE _ v w]
  show CompactAveraging.avgFormFamily (V := E) μ _ _ _ _ = _
  rw [CompactAveraging.avgFormFamily_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun γ =>
    (coordAction_pairing g₀ p₀ p hpE γ v w).symm)

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
by pushing forward along inversion.  Symmetry, positivity, invariance
(`avgMetricCompact_isRiemannianIsometry`), and smoothness of the averaged section
(the `contMDiff` field of `avgMetricCompact`, via `contMDiffOn_integral_scalar`) are all proved,
so the exercise is complete.  The boundaryless / second-countable hypotheses on the group hold
for every compact Lie group (Petersen's setting). -/
theorem exercise1_6_26 [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [CompactSpace Γ] [T2Space Γ] [SecondCountableTopology Γ] [I.Boundaryless] [J.Boundaryless]
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
