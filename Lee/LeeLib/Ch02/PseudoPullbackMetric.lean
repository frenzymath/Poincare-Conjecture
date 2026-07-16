/-
Chapter 2, "Riemannian Metrics", §"Pseudo-Riemannian Metrics": the tensor field induced on
a submanifold by an indefinite ambient metric, and the constructor that makes it a
`PseudoRiemannianMetric`.

Lee's Lemma 2.11 pulls a *Riemannian* metric back along an immersion, and
`LeeLib.Ch02.pullbackMetric` formalizes it.  The indefinite analogue is not a corollary,
and the reason is the whole point of Lee's §2.7: positive definiteness of a pullback is
equivalent to `F` being an immersion (`pullbackForm_posDef_iff_immersion`), so in the
Riemannian case the immersion hypothesis alone builds the metric.  Nondegeneracy of a
pullback is *not* implied by immersion — a nondegenerate form can restrict to a degenerate
one on a subspace, which is exactly why Lee's Proposition 2.70 exists — so the indefinite
constructor must take nondegeneracy as a hypothesis and the caller must earn it.

Everything except nondegeneracy is inherited.  Symmetry is immediate, and smoothness is
`contMDiff_pullbackFormOf`, which is stated for a bare smooth family of forms precisely so
that both the Riemannian and the indefinite pullback can use it without either reproving
the trivialization argument.

Why this file is needed at all: without it `IsPullbackAlong` — the hypothesis of Lee 2.70,
2.72 and 2.73 — has only one constructor, `isPullbackAlong_pullbackMetric`, which requires
a *Riemannian* ambient metric.  A caller with a genuinely indefinite `g̃` could therefore
never supply the hypothesis, and the pseudo-Riemannian submanifold theory, though it
typechecks, would apply to nothing indefinite.  `isPullbackAlong_pseudoPullbackMetric`
closes that gap.
-/

import LeeLib.Ch02.PseudoAdaptedFrame

namespace LeeLib.Ch02

open Bundle Module Manifold
open scoped Manifold ContDiff

section PseudoPullback

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **The pullback of an indefinite metric** `(F^* g̃)_p(v,w) = g̃_{F(p)}(dF_p v, dF_p w)`.

Lee's `ι^*g̃` for a pseudo-Riemannian ambient metric.  This is the same construction as
`pullbackForm`, on the `form` field instead of the `inner` field. -/
noncomputable def pseudoPullbackForm (g' : PseudoRiemannianMetric I' M') (F : M → M') (p : M) :
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  pullbackFormOf (fun y => g'.form y) F p

omit [IsManifold I ∞ M] in
@[simp] theorem pseudoPullbackForm_apply (g' : PseudoRiemannianMetric I' M') (F : M → M') (p : M)
    (v w : TangentSpace I p) :
    pseudoPullbackForm g' F p v w = g'.form (F p) (mfderiv I I' F p v) (mfderiv I I' F p w) :=
  rfl

omit [IsManifold I ∞ M] in
/-- The pullback form is symmetric, inherited from the symmetry of `g̃`. -/
theorem pseudoPullbackForm_symm (g' : PseudoRiemannianMetric I' M') (F : M → M') (p : M)
    (v w : TangentSpace I p) :
    pseudoPullbackForm g' F p v w = pseudoPullbackForm g' F p w v :=
  g'.symm _ _ _

/-- The pullback of an indefinite metric varies smoothly with the base point — the
indefinite case of `contMDiff_pullbackFormOf`.  Positivity is not used there, so this needs
no separate argument. -/
theorem pseudoPullbackForm_contMDiff (g' : PseudoRiemannianMetric I' M') {F : M → M'}
    (hF : ContMDiff I I' ∞ F) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ (⟨x, pseudoPullbackForm g' F x⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) :=
  contMDiff_pullbackFormOf (fun y => g'.form y) g'.contMDiff hF

/-- **The metric induced on a pseudo-Riemannian submanifold** — Lee's `ι^*g̃`, packaged as a
`PseudoRiemannianMetric` once the caller has established that it is nondegenerate.

Unlike the Riemannian `pullbackMetric`, which needs only that `F` be an immersion,
nondegeneracy is a genuine hypothesis here: it is *not* a consequence of `F` being an
immersion, and deciding it is the content of Lee's Proposition 2.70.  It is stated in the
witness form `∃ w, ...` that a construction can discharge, matching the `nondegenerate`
field of `Bundle.ContMDiffPseudoMetric`. -/
noncomputable def pseudoPullbackMetric (g' : PseudoRiemannianMetric I' M')
    (F : C^∞⟮I, M; I', M'⟯)
    (hnd : ∀ (p : M) (v : TangentSpace I p), v ≠ 0 →
      ∃ w, pseudoPullbackForm g' F p v w ≠ 0) :
    PseudoRiemannianMetric I M where
  form p := pseudoPullbackForm g' F p
  symm p v w := pseudoPullbackForm_symm g' F p v w
  nondegenerate := hnd
  contMDiff := pseudoPullbackForm_contMDiff g' F.contMDiff

@[simp] theorem pseudoPullbackMetric_form (g' : PseudoRiemannianMetric I' M')
    (F : C^∞⟮I, M; I', M'⟯)
    (hnd : ∀ (p : M) (v : TangentSpace I p), v ≠ 0 → ∃ w, pseudoPullbackForm g' F p v w ≠ 0)
    (p : M) :
    (pseudoPullbackMetric g' F hnd).form p = pseudoPullbackForm g' F p :=
  rfl

/-- **The induced metric of a pseudo-Riemannian submanifold is a pullback along the
inclusion** — the indefinite counterpart of `isPullbackAlong_pullbackMetric`.

This is what makes the pseudo-Riemannian submanifold theory usable for a genuinely
indefinite ambient metric.  Before it, `IsPullbackAlong` — the hypothesis of Lee 2.70, 2.72
and 2.73 — could only be discharged through `isPullbackAlong_pullbackMetric`, whose ambient
metric is Riemannian; so those results, while true, could only ever be applied to a
positive definite `g̃`, where 2.70's conclusion is vacuous (every normal is positive). -/
theorem isPullbackAlong_pseudoPullbackMetric (g' : PseudoRiemannianMetric I' M')
    (F : C^∞⟮I, M; I', M'⟯)
    (hnd : ∀ (p : M) (v : TangentSpace I p), v ≠ 0 → ∃ w, pseudoPullbackForm g' F p v w ≠ 0) :
    IsPullbackAlong I I' (pseudoPullbackMetric g' F hnd) g' F :=
  fun _ _ _ => rfl

end PseudoPullback

end LeeLib.Ch02
