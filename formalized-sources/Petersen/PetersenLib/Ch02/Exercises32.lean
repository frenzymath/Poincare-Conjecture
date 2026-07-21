import PetersenLib.Ch02.ChristoffelSymbols

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.32 (Leibniz rule for the tensor inner product)

Exercise 2.5.32: for tensors `S, T` of the same type,
`D_X g(S,T) = g(∇_X S, T) + g(S, ∇_X T)`.

Since the project has no basis-independent inner product on manifold tensor
*fields*, we contract against a chosen orthonormal frame `Efr`
(`tensorFieldMetricInner`), following the codebase's standing frame-as-hypothesis
pattern (as in `covariantDerivativeAdjoint` / `divergence_eq_neg_adjoint_dualForm`).
The Leibniz rule is then proved at a point `p` where the frame is *normal*
(`∇_v (Efr i) = 0`), exactly reproducing Petersen's own proof, in which the
connection (cross) terms drop because the frame is normal at the evaluation point.

Also included is `exists_localInverse_euclidean_of_hasDerivAt`, verified partial
progress toward Exercise 2.5.4 (the curve-straightening step): the reduction to a
`1`-D inverse function theorem giving a `C^∞` local inverse of `ℓ ∘ γ`. The full
Exercise 2.5.4 remains open — upgrading pointwise `C^∞` to open-neighbourhood
`C^∞` regularity hits a genuine mathlib gap (`ContDiffWithinAt.contDiffOn`
requires `m = ∞ → n = ω`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section
namespace PetersenLib
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- **The inner product of `(0,k)`-tensor fields against a given orthonormal
frame** (Petersen's `g(S,T)`, §2.2.4/§2.5 Ex. 32): the contraction of `S` and
`T` against every `k`-tuple of frame vectors, summed. -/
def tensorFieldMetricInner (Efr : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x)
    {k : ℕ} (S T : TensorOperator I M k) : M → ℝ :=
  fun x => ∑ σ : Fin k → Fin (Module.finrank ℝ E),
    S (fun j => Efr (σ j)) x * T (fun j => Efr (σ j)) x

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem isTensorOperator_slot_eq_zero_of_vanish {k : ℕ} {T : TensorOperator I M k}
    (hT : IsTensorOperator T) (Y : Fin k → Π x : M, TangentSpace I x) (i : Fin k) (x : M)
    (V : Π x : M, TangentSpace I x) (hV : V x = 0) :
    T (Function.update Y i V) x = 0 := by
  classical
  set c : M → ℝ := fun p => if p = x then 1 else 0 with hc_def
  have hgv : (fun p => c p • V p) = (fun p => (0 : TangentSpace I p)) := by
    funext p
    by_cases hp : p = x
    · subst hp; simp [hc_def, hV]
    · simp [hc_def, hp]
  have hkey := hT.smul_slot Y i c V x
  rw [hgv, hT.zero_slot Y i x] at hkey
  have hcx : c x = 1 := by simp [hc_def]
  rw [hcx, one_mul] at hkey
  exact hkey.symm

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem directionalDerivative_finset_sum {ι : Type} [DecidableEq ι] (s : Finset ι)
    (h : ι → M → ℝ) (x : M) (hh : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (h i) x)
    (Y : Π x : M, TangentSpace I x) :
    directionalDerivative Y (∑ i ∈ s, h i) x
      = ∑ i ∈ s, directionalDerivative Y (h i) x := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    rw [show (0 : M → ℝ) = (fun _ => (0:ℝ)) from rfl, directionalDerivative_const]
  | @insert a s' hins ih =>
    have hsub : ∀ i ∈ s', MDifferentiableAt I 𝓘(ℝ) (h i) x :=
      fun i hi => hh i (Finset.mem_insert_of_mem hi)
    have ha : MDifferentiableAt I 𝓘(ℝ) (h a) x := hh a (Finset.mem_insert_self a s')
    have hs' : MDifferentiableAt I 𝓘(ℝ) (∑ i ∈ s', h i) x := MDifferentiableAt.sum hsub
    rw [Finset.sum_insert hins, Finset.sum_insert hins, directionalDerivative_add ha hs' Y,
      ih hsub]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** **Exercise 2.5.32** (Leibniz rule for the inner product of tensors):
for `(0,k)`-tensors `S, T` and the pointwise inner product `g(S,T)` against an
orthonormal frame `Efr` that is *normal* at `p` (`∇_v (Efr i) = 0` for every
`v ∈ T_pM`, matching Petersen's proof via a frame normal at the evaluation
point), the Leibniz rule `D_X g(S,T) = g(∇_X S, T) + g(S, ∇_X T)` holds at `p`. -/
theorem exercise2_5_32 {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {k : ℕ} {S T : TensorOperator I M k} (hS : IsTensorOperator S) (hT : IsTensorOperator T)
    {Efr : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x}
    (hEfr : ∀ i, IsSmoothVectorField (Efr i))
    {X : Π x : M, TangentSpace I x}
    {p : M} (hNormal : ∀ i, ∀ v : TangentSpace I p, D.cov p v (Efr i) = 0) :
    directionalDerivative X (tensorFieldMetricInner Efr S T) p
      = tensorFieldMetricInner Efr (covariantDerivativeTensor D.toAffineConnection X S) T p
        + tensorFieldMetricInner Efr S (covariantDerivativeTensor D.toAffineConnection X T) p := by
  classical
  unfold tensorFieldMetricInner
  have hSsm : ∀ σ : Fin k → Fin (Module.finrank ℝ E),
      ContMDiff I 𝓘(ℝ) ∞ (S (fun j => Efr (σ j))) :=
    fun σ => hS.smooth_eval _ (fun j => hEfr (σ j))
  have hTsm : ∀ σ : Fin k → Fin (Module.finrank ℝ E),
      ContMDiff I 𝓘(ℝ) ∞ (T (fun j => Efr (σ j))) :=
    fun σ => hT.smooth_eval _ (fun j => hEfr (σ j))
  have hprod_diff : ∀ σ : Fin k → Fin (Module.finrank ℝ E),
      MDifferentiableAt I 𝓘(ℝ) (fun x => S (fun j => Efr (σ j)) x * T (fun j => Efr (σ j)) x) p :=
    fun σ => (((hSsm σ) p).mdifferentiableAt (by decide)).mul (((hTsm σ) p).mdifferentiableAt
      (by decide))
  have hrewrite : (fun x => ∑ σ : Fin k → Fin (Module.finrank ℝ E),
        S (fun j => Efr (σ j)) x * T (fun j => Efr (σ j)) x)
      = ∑ σ : Fin k → Fin (Module.finrank ℝ E),
        (fun x => S (fun j => Efr (σ j)) x * T (fun j => Efr (σ j)) x) := by
    funext x; simp [Finset.sum_apply]
  rw [hrewrite, directionalDerivative_finset_sum Finset.univ _ p (fun σ _ => hprod_diff σ)]
  have hterm : ∀ σ : Fin k → Fin (Module.finrank ℝ E),
      directionalDerivative X (fun x => S (fun j => Efr (σ j)) x * T (fun j => Efr (σ j)) x) p
        = covariantDerivativeTensor D.toAffineConnection X S (fun j => Efr (σ j)) p
            * T (fun j => Efr (σ j)) p
          + S (fun j => Efr (σ j)) p
            * covariantDerivativeTensor D.toAffineConnection X T (fun j => Efr (σ j)) p := by
    intro σ
    show directionalDerivative X (S (fun j => Efr (σ j)) * T (fun j => Efr (σ j))) p = _
    rw [directionalDerivative_mul (((hSsm σ) p).mdifferentiableAt (by decide))
      (((hTsm σ) p).mdifferentiableAt (by decide)) X]
    rw [covariantDerivativeTensor_formula, covariantDerivativeTensor_formula]
    have hcrossS : ∑ i, S (Function.update (fun j => Efr (σ j)) i
        (D.toAffineConnection.covField X (Efr (σ i)))) p = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply isTensorOperator_slot_eq_zero_of_vanish hS
      show D.toAffineConnection.cov p (X p) (Efr (σ i)) = 0
      exact hNormal (σ i) (X p)
    have hcrossT : ∑ i, T (Function.update (fun j => Efr (σ j)) i
        (D.toAffineConnection.covField X (Efr (σ i)))) p = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply isTensorOperator_slot_eq_zero_of_vanish hT
      show D.toAffineConnection.cov p (X p) (Efr (σ i)) = 0
      exact hNormal (σ i) (X p)
    rw [hcrossS, hcrossT]
    ring
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ), Finset.sum_add_distrib]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [ChartedSpace H M]
  [IsManifold I ∞ M] in
/-- **Partial progress toward Exercise 2.5.4** (Euclidean straightening step, NOT a
full closure of the exercise): if `γ : ℝ → E` is smooth with `γ'(t₀) = v`, and
`ℓ : E →L[ℝ] ℝ` is a linear functional with `ℓ(v) ≠ 0`, then `h := ℓ ∘ γ : ℝ → ℝ` has a
`C^∞` local inverse `ψ` at the point `ℓ(γ t₀)` (pointwise regularity via the real
inverse function theorem), with `ψ (ℓ (γ t)) = t` for `t` near `t₀`. -/
theorem exists_localInverse_euclidean_of_hasDerivAt
    (γ : ℝ → E) (t₀ : ℝ) (hγ : ContDiff ℝ ∞ γ) {v : E}
    (hderiv : HasDerivAt γ v t₀) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v ≠ 0) :
    ∃ ψ : ℝ → ℝ, ContDiffAt ℝ ∞ ψ (ℓ (γ t₀)) ∧ ∀ᶠ t in nhds t₀, ψ (ℓ (γ t)) = t := by
  classical
  set h : ℝ → ℝ := fun t => ℓ (γ t) with hdef
  have hh : ContDiff ℝ ∞ h := ℓ.contDiff.comp hγ
  have hderivh : HasDerivAt h (ℓ v) t₀ := by
    have := (ℓ.hasFDerivAt).comp_hasDerivAt t₀ hderiv
    simpa [hdef] using this
  set f' : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ (ℓ v) hℓ).toContinuousLinearEquiv
    with hf'def
  have hf'coe : (f' : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (ℓ v) := by
    apply ContinuousLinearMap.ext
    intro x
    rw [hf'def]
    have heq : ((LinearEquiv.smulOfNeZero ℝ ℝ (ℓ v) hℓ).toContinuousLinearEquiv : ℝ → ℝ) x
        = (LinearEquiv.smulOfNeZero ℝ ℝ (ℓ v) hℓ) x :=
      congrFun (LinearEquiv.coe_toContinuousLinearEquiv'
        (LinearEquiv.smulOfNeZero ℝ ℝ (ℓ v) hℓ)) x
    rw [show ((LinearEquiv.smulOfNeZero ℝ ℝ (ℓ v) hℓ).toContinuousLinearEquiv : ℝ →L[ℝ] ℝ) x
      = ((LinearEquiv.smulOfNeZero ℝ ℝ (ℓ v) hℓ).toContinuousLinearEquiv : ℝ → ℝ) x from rfl,
      heq, LinearEquiv.smulOfNeZero_apply]
    simp [smul_eq_mul, mul_comm]
  have hfderiv : HasFDerivAt h (f' : ℝ →L[ℝ] ℝ) t₀ := by
    rw [hf'coe]; exact hderivh.hasFDerivAt
  have hCat : ContDiffAt ℝ ∞ h t₀ := hh.contDiffAt
  refine ⟨ContDiffAt.localInverse hCat hfderiv (by simp), ?_, ?_⟩
  · exact ContDiffAt.to_localInverse hCat hfderiv (by simp)
  · exact HasStrictFDerivAt.eventually_left_inverse
      (hCat.hasStrictFDerivAt' hfderiv (by simp))
end PetersenLib
end
