import PetersenLib.Ch01.ArcLength

/-!
# Petersen Ch. 1, Exercise 1.6.26 — averaging a metric over a group action

Petersen's Exercise 1.6.26 asks: if a **compact** group `Γ` acts on a manifold `M`, then `M`
carries a Riemannian metric for which `Γ` acts by isometries.  The recipe is: take any metric
`g₀` (one exists by a partition of unity, `PetersenLib.exists_riemannianMetric`) and average
its pullbacks over the group,

  `g(u, v) = ∫_Γ g₀(Dγ(u), Dγ(v)) dμ(γ)`,

against the Haar probability measure `μ` of `Γ`.

This file carries out the averaging in the case where `Γ` is **finite**, where the integral is
a finite sum and no measure theory is needed at all:

  `g(u, v) = ∑_{γ ∈ Γ} g₀(Dγ(u), Dγ(v))`.

Everything that makes the argument work is already visible here: each summand is the pullback
form `γ^*g₀` (symmetric, positive definite because `γ` is a diffeomorphism, and smooth by
`pullbackForm_contMDiff`), the sum of finitely many smooth sections is smooth
(`ContMDiff.add_section`), and invariance is the *reindexing* `γ ↦ γδ` of the sum together with
the chain rule `D(γ·)∘D(δ·) = D((γδ)·)`.

For a general compact `Γ` the same three steps are needed, but the sum becomes a Haar integral.
The fibrewise averaging — symmetry and positive-definiteness of `(u, v) ↦ ∫_Γ (γ^*g₀)_p(u, v) dμ`
— is supplied sorry-free by `PetersenLib.CompactAveraging.avgFormFamily`
(`PetersenLib/Ch01/BiinvariantAveraging.lean`).  What remains is (i) continuity in `γ` of the
fibre form (the partial tangent map of the action, via `ContMDiffAt.mfderiv`) and (ii) the
smoothness step, which needs a `C^∞` parametric-integral theorem for sections of a vector bundle —
infrastructure Mathlib does not have (`Mathlib/Analysis/Calculus/ParametricIntegral.lean` provides
only first derivatives).  Step (ii) is the sole irreducible obstruction to `exercise1_6_26`; see
its docstring.

The finite case is not a toy: it is exactly what the deck group of a finite covering needs
(Petersen Example 1.3.7, `RP^n = S^n/{±1}`), and it is the case in which `quotientMetric`
is applied.

Main results:

* `actionDiffeomorph` — the action of `γ ∈ Γ` as a `Diffeomorph`, when it is smooth.
* `averagedMetric` — the metric `∑_γ γ^*g₀`.
* `averagedMetric_isRiemannianIsometry` — `Γ` acts by isometries for it.
* `exercise1_6_26_finite` — Exercise 1.6.26 for a finite group.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Exercise 1.6.26.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped ContDiff Manifold

namespace PetersenLib

section Averaging

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {Γ : Type*} [Group Γ] [MulAction Γ M]

/-! ## The action of a group element as a diffeomorphism -/

variable (I) in
/-- **Math.** If every element of `Γ` acts smoothly on `M`, then each `γ` acts as a
**diffeomorphism**: `γ⁻¹ ·` is a smooth two-sided inverse of `γ ·`. -/
def actionDiffeomorph (hs : ∀ γ : Γ, ContMDiff I I ∞ (fun p : M => γ • p)) (γ : Γ) :
    Diffeomorph I I M M ∞ where
  toEquiv := MulAction.toPerm γ
  contMDiff_toFun := hs γ
  contMDiff_invFun := hs γ⁻¹

/-- **Eng.** The differential of `p ↦ γ • p` is injective at every point: the chain rule applied
to `(γ⁻¹ ·) ∘ (γ ·) = id` exhibits a left inverse for it. -/
theorem mfderiv_smul_injective (hs : ∀ γ : Γ, ContMDiff I I ∞ (fun p : M => γ • p))
    (γ : Γ) (p : M) :
    Function.Injective (mfderiv I I (fun q : M => γ • q) p) := by
  have hγ : MDifferentiableAt I I (fun q : M => γ • q) p :=
    (hs γ p).mdifferentiableAt (by simp)
  have hγinv : MDifferentiableAt I I (fun q : M => γ⁻¹ • q) (γ • p) :=
    (hs γ⁻¹ (γ • p)).mdifferentiableAt (by simp)
  have hcomp : (fun q : M => γ⁻¹ • q) ∘ (fun q : M => γ • q) = id := by
    funext q
    simp [smul_smul]
  have hchain := mfderiv_comp (I := I) (I' := I) (I'' := I) p hγinv hγ
  rw [hcomp, mfderiv_id] at hchain
  intro u v huv
  have h1 : mfderiv I I (fun q : M => γ⁻¹ • q) (γ • p)
      (mfderiv I I (fun q : M => γ • q) p u) = u := by
    have := congrArg (fun L : TangentSpace I p →L[ℝ] TangentSpace I p => L u) hchain.symm
    simpa using this
  have h2 : mfderiv I I (fun q : M => γ⁻¹ • q) (γ • p)
      (mfderiv I I (fun q : M => γ • q) p v) = v := by
    have := congrArg (fun L : TangentSpace I p →L[ℝ] TangentSpace I p => L v) hchain.symm
    simpa using this
  rw [← h1, ← h2, huv]

/-- **Eng.** `p ↦ γ • p` is a smooth immersion (indeed a diffeomorphism), so its pullback form is
a metric. -/
theorem isSmoothImmersion_smul (hs : ∀ γ : Γ, ContMDiff I I ∞ (fun p : M => γ • p)) (γ : Γ) :
    IsSmoothImmersion (I := I) (I' := I) (fun p : M => γ • p) :=
  ⟨hs γ, fun p => mfderiv_smul_injective hs γ p⟩

/-! ## Smoothness of a finite sum of sections -/

variable [FiniteDimensional ℝ E]

/-- **Eng.** A finite sum of smooth sections of the bilinear-form bundle over `M` is a smooth
section: induct on the index finset with `ContMDiff.add_section`, the empty sum being the
(smooth) zero section. -/
theorem contMDiff_finsetSum_section {ι : Type*} (s : Finset ι)
    (f : ι → ∀ p : M, TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ)
    (hf : ∀ i ∈ s, ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p ↦ (⟨p, f i p⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun p ↦ TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ)))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p ↦ (⟨p, (∑ i ∈ s, f i) p⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun p ↦ TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 := Bundle.contMDiff_zeroSection (𝕜 := ℝ) (IB := I) (n := ∞)
        (F := E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun p : M => TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ)
      simpa [Bundle.zeroSection] using h0
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact ContMDiff.add_section (hf i (Finset.mem_insert_self i s))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-! ## The averaged form -/

variable [Fintype Γ]

variable (I) in
/-- **Math.** Petersen Exercise 1.6.26 (finite case): the **average of `g₀` over `Γ`**,
`g(u, v) = ∑_{γ ∈ Γ} g₀(Dγ(u), Dγ(v))` — the finite sum of the pullbacks `γ^*g₀`. -/
def averagedForm (g₀ : RiemannianMetric I M) :
    ∀ p : M, TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  ∑ γ : Γ, fun p => pullbackForm (I := I) g₀ (fun q : M => γ • q) p

theorem averagedForm_apply (g₀ : RiemannianMetric I M) (p : M) (u v : TangentSpace I p) :
    averagedForm I (Γ := Γ) g₀ p u v
      = ∑ γ : Γ, g₀.metricInner (γ • p)
          (mfderiv I I (fun q : M => γ • q) p u) (mfderiv I I (fun q : M => γ • q) p v) := by
  show (∑ γ : Γ, fun p => pullbackForm (I := I) g₀ (fun q : M => γ • q) p) p u v = _
  rw [Finset.sum_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply]
  rfl

/-- **Math.** The averaged form is symmetric: each pullback `γ^*g₀` is. -/
theorem averagedForm_symm (g₀ : RiemannianMetric I M) (p : M) (u v : TangentSpace I p) :
    averagedForm I (Γ := Γ) g₀ p u v = averagedForm I (Γ := Γ) g₀ p v u := by
  rw [averagedForm_apply, averagedForm_apply]
  exact Finset.sum_congr rfl fun γ _ => g₀.symm _ _ _

/-- **Math.** The averaged form is positive definite: each `γ` acts by a diffeomorphism, so
`Dγ(u) ≠ 0` whenever `u ≠ 0` and *every* summand `g₀(Dγ u, Dγ u)` is already strictly positive
(the sum is over the nonempty index set `Γ`). -/
theorem averagedForm_self_pos (g₀ : RiemannianMetric I M)
    (hs : ∀ γ : Γ, ContMDiff I I ∞ (fun p : M => γ • p))
    (p : M) (u : TangentSpace I p) (hu : u ≠ 0) :
    0 < averagedForm I (Γ := Γ) g₀ p u u := by
  rw [averagedForm_apply]
  refine Finset.sum_pos (fun γ _ => ?_) Finset.univ_nonempty
  exact g₀.metricInner_self_pos _ _ (fun h => hu (mfderiv_smul_injective hs γ p (by simpa using h)))

/-- **Eng.** The averaged form is a smooth section of the bilinear-form bundle: a finite sum of
the smooth pullback sections `γ^*g₀` (`pullbackForm_contMDiff`). -/
theorem averagedForm_contMDiff (g₀ : RiemannianMetric I M)
    (hs : ∀ γ : Γ, ContMDiff I I ∞ (fun p : M => γ • p)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p ↦ (⟨p, averagedForm I (Γ := Γ) g₀ p⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun p ↦ TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ))) :=
  contMDiff_finsetSum_section Finset.univ
    (fun γ p => pullbackForm (I := I) g₀ (fun q : M => γ • q) p)
    (fun γ _ => pullbackForm_contMDiff g₀ (hs γ))

variable (I) in
/-- **Math.** Petersen Exercise 1.6.26 (finite case): the **averaged metric**
`g = ∑_{γ ∈ Γ} γ^*g₀` on `M`.  It is symmetric and positive definite termwise, and smooth as a
finite sum of smooth pullback sections. -/
def averagedMetric (g₀ : RiemannianMetric I M)
    (hs : ∀ γ : Γ, ContMDiff I I ∞ (fun p : M => γ • p)) :
    RiemannianMetric I M where
  inner p := averagedForm I (Γ := Γ) g₀ p
  symm p u v := averagedForm_symm g₀ p u v
  pos p u hu := averagedForm_self_pos g₀ hs p u hu
  isVonNBounded p := by
    refine isVonNBounded_of_posDef (E := E) (averagedForm I (Γ := Γ) g₀ p) (fun u hu => ?_)
    exact averagedForm_self_pos g₀ hs p u hu
  contMDiff := averagedForm_contMDiff g₀ hs

@[simp]
theorem averagedMetric_apply (g₀ : RiemannianMetric I M)
    (hs : ∀ γ : Γ, ContMDiff I I ∞ (fun p : M => γ • p)) (p : M) (u v : TangentSpace I p) :
    (averagedMetric I g₀ hs).metricInner p u v
      = ∑ γ : Γ, g₀.metricInner (γ • p)
          (mfderiv I I (fun q : M => γ • q) p u) (mfderiv I I (fun q : M => γ • q) p v) :=
  averagedForm_apply g₀ p u v

/-! ## `Γ` acts by isometries for the averaged metric -/

/-- **Math.** Petersen Exercise 1.6.26 (the invariance step): the averaged metric is
`Γ`-invariant.  Indeed `D(γ ·)_{δ·p} ∘ D(δ ·)_p = D((γδ) ·)_p` by the chain rule, so the
`γ`-summand at `δ • p`, evaluated on `Dδ(u), Dδ(v)`, is the `γδ`-summand at `p` evaluated on
`u, v`; summing and reindexing by the bijection `γ ↦ γδ` of `Γ` returns the original sum. -/
theorem averagedMetric_preservesMetric (g₀ : RiemannianMetric I M)
    (hs : ∀ γ : Γ, ContMDiff I I ∞ (fun p : M => γ • p)) (δ : Γ) :
    PreservesMetric (averagedMetric I g₀ hs) (averagedMetric I g₀ hs) (fun p : M => δ • p) := by
  intro p u v
  have hδ : MDifferentiableAt I I (fun q : M => δ • q) p :=
    (hs δ p).mdifferentiableAt (by simp)
  -- the chain rule, one group element at a time
  have hchain : ∀ γ : Γ, ∀ w : TangentSpace I p,
      mfderiv I I (fun q : M => γ • q) (δ • p) (mfderiv I I (fun q : M => δ • q) p w)
        = mfderiv I I (fun q : M => (γ * δ) • q) p w := by
    intro γ w
    have hγ : MDifferentiableAt I I (fun q : M => γ • q) (δ • p) :=
      (hs γ (δ • p)).mdifferentiableAt (by simp)
    have hcomp : (fun q : M => γ • q) ∘ (fun q : M => δ • q) = fun q : M => (γ * δ) • q := by
      funext q
      rw [Function.comp_apply, smul_smul]
    have h := mfderiv_comp (I := I) (I' := I) (I'' := I) p hγ hδ
    rw [hcomp] at h
    exact congrArg (fun L : TangentSpace I p →L[ℝ] TangentSpace I (δ • p) => L w) h.symm
  rw [averagedMetric_apply, averagedMetric_apply]
  -- rewrite each summand at `δ • p` as the `γδ`-summand at `p`
  have hterm : ∀ γ : Γ,
      g₀.metricInner (γ • (δ • p))
          (mfderiv I I (fun q : M => γ • q) (δ • p) (mfderiv I I (fun q : M => δ • q) p u))
          (mfderiv I I (fun q : M => γ • q) (δ • p) (mfderiv I I (fun q : M => δ • q) p v))
        = g₀.metricInner ((γ * δ) • p)
            (mfderiv I I (fun q : M => (γ * δ) • q) p u)
            (mfderiv I I (fun q : M => (γ * δ) • q) p v) := by
    intro γ
    rw [hchain γ u, hchain γ v, smul_smul]
  rw [Finset.sum_congr rfl (fun γ _ => hterm γ)]
  -- reindex `γ ↦ γδ`
  exact (Fintype.sum_equiv (Equiv.mulRight δ)
    (fun γ : Γ => g₀.metricInner ((γ * δ) • p)
      (mfderiv I I (fun q : M => (γ * δ) • q) p u)
      (mfderiv I I (fun q : M => (γ * δ) • q) p v))
    (fun γ : Γ => g₀.metricInner (γ • p)
      (mfderiv I I (fun q : M => γ • q) p u) (mfderiv I I (fun q : M => γ • q) p v))
    (fun γ => rfl)).symm

/-- **Math.** Petersen Exercise 1.6.26 (finite case): for the averaged metric `∑_γ γ^*g₀`, every
element of `Γ` acts as a **Riemannian isometry** — it is a diffeomorphism (`actionDiffeomorph`)
and it preserves the metric (`averagedMetric_preservesMetric`). -/
theorem averagedMetric_isRiemannianIsometry (g₀ : RiemannianMetric I M)
    (hs : ∀ γ : Γ, ContMDiff I I ∞ (fun p : M => γ • p)) (δ : Γ) :
    IsRiemannianIsometry (averagedMetric I g₀ hs) (averagedMetric I g₀ hs)
      (fun p : M => δ • p) :=
  ⟨⟨actionDiffeomorph I hs δ, rfl⟩, averagedMetric_preservesMetric g₀ hs δ⟩

/-! ## Exercise 1.6.26 for a finite group -/

variable [T2Space M] [SigmaCompactSpace M]

/-- **Math.** Petersen Exercise 1.6.26, **finite case**: if a finite group `Γ` acts smoothly on a
manifold `M`, then `M` carries a Riemannian metric for which `Γ` acts by isometries.  Take any
metric `g₀` (`exists_riemannianMetric`, via a partition of unity) and average it over `Γ`.

A finite group *is* a compact group, so this is a genuine special case of Petersen's exercise;
the general compact case is `exercise1_6_26`, still open because averaging against Haar measure
needs a `C^∞` parametric-integral theorem for bundle-valued sections that Mathlib lacks.  Every
other ingredient of the argument — symmetry, positivity, smoothness of the average, and the
reindexing that yields invariance — is already proved here in the finite case and carries over
verbatim once that integral is available. -/
theorem exercise1_6_26_finite {Γ : Type*} [Group Γ] [Fintype Γ] [MulAction Γ M]
    (hs : ∀ γ : Γ, ContMDiff I I ∞ (fun p : M => γ • p)) :
    ∃ g : RiemannianMetric I M, ∀ γ : Γ,
      IsRiemannianIsometry g g (fun p : M => γ • p) := by
  obtain ⟨g₀⟩ := exists_riemannianMetric (I := I) (M := M)
  exact ⟨averagedMetric I g₀ hs, fun γ => averagedMetric_isRiemannianIsometry g₀ hs γ⟩

end Averaging

end PetersenLib
