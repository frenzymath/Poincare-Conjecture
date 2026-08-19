import MorganTianLib.Ch02.LaplacianExtremum
import Topping.MaximumPrinciple.Core

/-!
# Riemannian input to the weak maximum principle

This module reduces a scalar parabolic inequality at a spatial maximum to its
reaction term. The vanishing differential and nonpositive Laplacian are supplied
by the shared Morgan-Tian extremum theorem.
-/

open scoped ContDiff Manifold Topology Bundle
open Set Riemannian

noncomputable section

namespace Topping

/-- **Math.** The Laplace--Beltrami operator, with the empty trace in
dimension zero. -/
noncomputable def metricLaplacianAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g : RiemannianMetric I M) (f : M → ℝ) (p : M) : ℝ :=
  if h : Module.finrank ℝ E = 0 then 0 else
    letI : NeZero (Module.finrank ℝ E) := ⟨h⟩
    MorganTianLib.laplacianAt g g.leviCivitaConnection f p

/-- **Math.** The metric Laplacian is linear under negation, including when
the model space has dimension zero. -/
theorem metricLaplacianAt_neg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g : RiemannianMetric I M) (f : M → ℝ) (p : M) :
    metricLaplacianAt g (fun q => -f q) p = -metricLaplacianAt g f p := by
  by_cases hdim : Module.finrank ℝ E = 0
  · simp [metricLaplacianAt, hdim]
  · letI : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    simp only [metricLaplacianAt, hdim, ↓reduceDIte]
    unfold MorganTianLib.laplacianAt
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    unfold MorganTianLib.hessianAt MorganTianLib.hessian
    have hdir (Y : SmoothVectorField I M) (k : M → ℝ) :
        Y.dir (fun q => -k q) = fun q => -Y.dir k q := by
      funext q
      simp only [SmoothVectorField.dir]
      rw [show (fun y => -k y) = -k by rfl, mfderiv_neg]
      rfl
    rw [hdir, hdir, hdir]
    ring

/-- **Math.** The metric Laplacian is additive in the function.  Like negation,
this reduces to additivity of directional derivatives inside the trace, and holds
in dimension zero because both sides vanish. -/
theorem metricLaplacianAt_add
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g : RiemannianMetric I M) {f₁ f₂ : M → ℝ}
    (hf₁ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₁) (hf₂ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₂) (p : M) :
    metricLaplacianAt g (fun q => f₁ q + f₂ q) p =
      metricLaplacianAt g f₁ p + metricLaplacianAt g f₂ p := by
  by_cases hdim : Module.finrank ℝ E = 0
  · simp [metricLaplacianAt, hdim]
  · letI : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    simp only [metricLaplacianAt, hdim, ↓reduceDIte]
    unfold MorganTianLib.laplacianAt
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    unfold MorganTianLib.hessianAt MorganTianLib.hessian
    have hdir (Y : SmoothVectorField I M) {k₁ k₂ : M → ℝ}
        (hk₁ : ContMDiff I 𝓘(ℝ, ℝ) ∞ k₁) (hk₂ : ContMDiff I 𝓘(ℝ, ℝ) ∞ k₂) :
        Y.dir (fun q => k₁ q + k₂ q) = fun q => Y.dir k₁ q + Y.dir k₂ q := by
      funext q
      exact Y.dir_add q (hk₁.mdifferentiableAt (by norm_num))
        (hk₂.mdifferentiableAt (by norm_num))
    have hsm (Y : SmoothVectorField I M) {k : M → ℝ}
        (hk : ContMDiff I 𝓘(ℝ, ℝ) ∞ k) :
        ContMDiff I 𝓘(ℝ, ℝ) ∞ (Y.dir k) := Y.dir_contMDiff hk
    rw [hdir _ hf₁ hf₂, hdir _ (hsm _ hf₁) (hsm _ hf₂),
      hdir _ hf₁ hf₂]
    ring

/-- **Math.** The metric Laplacian is homogeneous in the function. -/
theorem metricLaplacianAt_const_mul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g : RiemannianMetric I M) (c : ℝ) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    metricLaplacianAt g (fun q => c * f q) p =
      c * metricLaplacianAt g f p := by
  by_cases hdim : Module.finrank ℝ E = 0
  · simp [metricLaplacianAt, hdim]
  · letI : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    simp only [metricLaplacianAt, hdim, ↓reduceDIte]
    unfold MorganTianLib.laplacianAt
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    unfold MorganTianLib.hessianAt MorganTianLib.hessian
    have hdir (Y : SmoothVectorField I M) {k : M → ℝ}
        (hk : ContMDiff I 𝓘(ℝ, ℝ) ∞ k) :
        Y.dir (fun q => c * k q) = fun q => c * Y.dir k q := by
      funext q
      exact Y.dir_const_mul c q (hk.mdifferentiableAt (by norm_num))
    have hsm (Y : SmoothVectorField I M) {k : M → ℝ}
        (hk : ContMDiff I 𝓘(ℝ, ℝ) ∞ k) :
        ContMDiff I 𝓘(ℝ, ℝ) ∞ (Y.dir k) := Y.dir_contMDiff hk
    rw [hdir _ hf, hdir _ (hsm _ hf), hdir _ hf]
    ring

/-- **Math.** The metric Laplacian is linear in a finite sum of smooth functions.
The Bernstein--Bando--Shi cascade needs this at the whole telescoping combination
`Σ_j a_j t^j |∇^j\Rm|^2` at once, not one summand at a time. Like the binary case
it holds in dimension zero because both sides vanish. -/
theorem metricLaplacianAt_finsetSum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g : RiemannianMetric I M) {ι : Type*} (s : Finset ι) {f : ι → M → ℝ}
    (hf : ∀ i ∈ s, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f i)) (p : M) :
    metricLaplacianAt g (fun q => ∑ i ∈ s, f i q) p =
      ∑ i ∈ s, metricLaplacianAt g (f i) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h := metricLaplacianAt_const_mul g (0 : ℝ)
        (f := fun _ : M => (0 : ℝ)) contMDiff_const p
      simpa using h
  | @insert a s ha ih =>
      have hfa : ContMDiff I 𝓘(ℝ, ℝ) ∞ (f a) := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f i) :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hsum : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => ∑ i ∈ s, f i q) := by
        have h := Finset.sum_induction f (fun k => ContMDiff I 𝓘(ℝ, ℝ) ∞ k)
          (fun _ _ h₁ h₂ => h₁.add h₂) contMDiff_const hfs
        rw [show (fun q => ∑ i ∈ s, f i q) = (∑ i ∈ s, f i) from
          funext fun q => (Finset.sum_apply q s f).symm]
        exact h
      have hrw : (fun q => ∑ i ∈ insert a s, f i q)
          = fun q => f a q + ∑ i ∈ s, f i q := by
        funext q; rw [Finset.sum_insert ha]
      rw [hrw, metricLaplacianAt_add g hfa hsum p, ih hfs,
        Finset.sum_insert ha]

/-- **Math.** At a local maximum, the differential vanishes and the metric
Laplacian is nonpositive, including in dimension zero. -/
theorem metricLaplacianAt_nonpos_of_isLocalMax
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    (g : RiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {q : M}
    (hmax : IsLocalMax f q) :
    mfderiv I 𝓘(ℝ, ℝ) f q = 0 ∧ metricLaplacianAt g f q ≤ 0 := by
  by_cases hdim : Module.finrank ℝ E = 0
  · refine ⟨MorganTianLib.mfderiv_eq_zero_of_isLocalMax hf hmax, ?_⟩
    simp [metricLaplacianAt, hdim]
  · letI : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    simpa [metricLaplacianAt, hdim] using
      MorganTianLib.laplacianAt_nonpos_of_isLocalMax
        g g.leviCivitaConnection hf hmax

/-- **Math.** At a spatial local maximum, the diffusion and drift terms in a
scalar parabolic inequality are nonpositive and zero, respectively. -/
theorem time_deriv_le_reaction_of_isLocalMax
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M]
    (g : RiemannianMetric I M) (X : SmoothVectorField I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {q : M}
    (hmax : IsLocalMax f q) {ut reaction : ℝ}
    (hsub : ut ≤ metricLaplacianAt g f q
      + X.dir f q + reaction) :
    ut ≤ reaction := by
  obtain ⟨hdf, hlaplacian⟩ :=
    metricLaplacianAt_nonpos_of_isLocalMax g hf hmax
  have hdrift : X.dir f q = 0 := by
    exact congrArg (fun L => L (X q)) hdf
  rw [hdrift] at hsub
  linarith

/-- **Math.** A smooth spacetime function restricts to a smooth spatial slice
at every time in the interval. -/
theorem contMDiff_spatial_slice_of_contMDiffOn_spacetime
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {u : M → ℝ → ℝ} {T t : ℝ}
    (hu : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => u z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (ht : t ∈ Icc 0 T) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ fun x => u x t := by
  have hi : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun x : M => (x, t)) :=
    contMDiff_id.prodMk contMDiff_const
  have hc : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      ((fun z : M × ℝ => u z.1 z.2) ∘ fun x : M => (x, t)) Set.univ :=
    hu.comp (s := Set.univ) hi.contMDiffOn
      (fun x _hx => ⟨mem_univ x, ht⟩)
  rw [contMDiffOn_univ] at hc
  simpa [Function.comp_def] using hc

/-- **Math.** A smooth spacetime function restricts to a smooth time curve on
the closed time interval. -/
theorem contDiffOn_time_slice_of_contMDiffOn_spacetime
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {u : M → ℝ → ℝ} {T : ℝ}
    (hu : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => u z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (x : M) :
    ContDiffOn ℝ ∞ (u x) (Icc 0 T) := by
  intro t ht
  have hi : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun s : ℝ => (x, s)) :=
    contMDiff_const.prodMk contMDiff_id
  have hc := hu.comp (s := Icc 0 T) hi.contMDiffOn
    (fun s hs => ⟨mem_univ x, hs⟩)
  have hct := hc t ht
  simpa [Function.comp_def] using hct.contDiffWithinAt

/-- **Math.** Parabolic ODE comparison when the differential inequality is
available only at strictly positive times. This is the natural endpoint
interface for an evolution equation proved on the interior of a forward time
interval: the contradiction argument never uses the equation at `t = 0`. -/
theorem le_ode_solution_of_parabolic_inequality_of_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
    {g : ℝ → RiemannianMetric I M}
    {X : ℝ → SmoothVectorField I M}
    {u ut : M → ℝ → ℝ} {φ φ' : ℝ → ℝ}
    {F : ℝ → ℝ → ℝ} {T K : ℝ}
    (hT : 0 ≤ T)
    (hcont : ContinuousOn (fun z : M × ℝ => u z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hspace : ∀ t ∈ Icc 0 T,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ fun x => u x t)
    (huderiv : ∀ x t, t ∈ Icc 0 T →
      HasDerivWithinAt (u x) (ut x t) (Icc 0 T) t)
    (hφderiv : ∀ t, t ∈ Icc 0 T →
      HasDerivWithinAt φ (φ' t) (Icc 0 T) t)
    (hode : ∀ t ∈ Icc 0 T, φ' t = F (φ t) t)
    (hpde : ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      ut x t ≤ metricLaplacianAt (g t) (fun y => u y t) x
        + (X t).dir (fun y => u y t) x + F (u x t) t)
    (hreaction : ∀ t ∈ Icc 0 T, ∀ x, φ t < u x t →
      F (u x t) t - F (φ t) t ≤ K * (u x t - φ t))
    (hzero : ∀ x, u x 0 ≤ φ 0) :
    ∀ x t, t ∈ Icc 0 T → u x t ≤ φ t := by
  apply le_ode_solution_of_forall_isMax_time_deriv_le_of_pos
    hT hcont huderiv hφderiv hode ?_ hreaction hzero
  intro t ht htpos x _hxpos hxmax
  apply time_deriv_le_reaction_of_isLocalMax
    (g t) (X t) (hspace t ht)
    (hsub := hpde t ht htpos x)
  exact Filter.Eventually.of_forall hxmax

/-- **Math.** A scalar parabolic inequality on a compact Riemannian manifold
reduces to nonlinear ODE comparison once the reaction has a one-sided
Lipschitz bound along the compared values. -/
theorem le_ode_solution_of_parabolic_inequality
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
    {g : ℝ → RiemannianMetric I M}
    {X : ℝ → SmoothVectorField I M}
    {u ut : M → ℝ → ℝ} {φ φ' : ℝ → ℝ}
    {F : ℝ → ℝ → ℝ} {T K : ℝ}
    (hT : 0 ≤ T)
    (hcont : ContinuousOn (fun z : M × ℝ => u z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hspace : ∀ t ∈ Icc 0 T,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ fun x => u x t)
    (huderiv : ∀ x t, t ∈ Icc 0 T →
      HasDerivWithinAt (u x) (ut x t) (Icc 0 T) t)
    (hφderiv : ∀ t, t ∈ Icc 0 T →
      HasDerivWithinAt φ (φ' t) (Icc 0 T) t)
    (hode : ∀ t ∈ Icc 0 T, φ' t = F (φ t) t)
    (hpde : ∀ t ∈ Icc 0 T, ∀ x,
      ut x t ≤ metricLaplacianAt (g t) (fun y => u y t) x
        + (X t).dir (fun y => u y t) x + F (u x t) t)
    (hreaction : ∀ t ∈ Icc 0 T, ∀ x, φ t < u x t →
      F (u x t) t - F (φ t) t ≤ K * (u x t - φ t))
    (hzero : ∀ x, u x 0 ≤ φ 0) :
    ∀ x t, t ∈ Icc 0 T → u x t ≤ φ t := by
  apply le_ode_solution_of_forall_isMax_time_deriv_le
    hT hcont huderiv hφderiv hode ?_ hreaction hzero
  intro t ht x _hxpos hxmax
  apply time_deriv_le_reaction_of_isLocalMax
    (g t) (X t) (hspace t ht)
    (hsub := hpde t ht x)
  exact Filter.Eventually.of_forall hxmax

/-- **Math.** On a common compact range for `u` and the comparison solution,
continuous differentiability of the reaction supplies the one-sided bound
needed by `le_ode_solution_of_parabolic_inequality`. -/
theorem le_ode_solution_of_parabolic_inequality_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
    {g : ℝ → RiemannianMetric I M}
    {X : ℝ → SmoothVectorField I M}
    {u ut : M → ℝ → ℝ} {φ φ' : ℝ → ℝ}
    {F : ℝ → ℝ → ℝ} {T a b : ℝ}
    (hT : 0 ≤ T)
    (hcont : ContinuousOn (fun z : M × ℝ => u z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hspace : ∀ t ∈ Icc 0 T,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ fun x => u x t)
    (huderiv : ∀ x t, t ∈ Icc 0 T →
      HasDerivWithinAt (u x) (ut x t) (Icc 0 T) t)
    (hφderiv : ∀ t, t ∈ Icc 0 T →
      HasDerivWithinAt φ (φ' t) (Icc 0 T) t)
    (hode : ∀ t ∈ Icc 0 T, φ' t = F (φ t) t)
    (hF : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => F z.1 z.2)
      (Icc a b ×ˢ Icc 0 T))
    (hu_range : ∀ x t, t ∈ Icc 0 T → u x t ∈ Icc a b)
    (hφ_range : ∀ t, t ∈ Icc 0 T → φ t ∈ Icc a b)
    (hpde : ∀ t ∈ Icc 0 T, ∀ x,
      ut x t ≤ metricLaplacianAt (g t) (fun y => u y t) x
        + (X t).dir (fun y => u y t) x + F (u x t) t)
    (hzero : ∀ x, u x 0 ≤ φ 0) :
    ∀ x t, t ∈ Icc 0 T → u x t ≤ φ t := by
  obtain ⟨K, _hK, hreaction⟩ :=
    exists_nonneg_reaction_bound_on_rectangle hF
  apply le_ode_solution_of_parabolic_inequality
    (K := K) hT hcont hspace huderiv hφderiv hode hpde ?_ hzero
  intro t ht x hφu
  exact hreaction t ht (u x t) (hu_range x t ht)
    (φ t) (hφ_range t ht) hφu.le

/-- **Math.** Smoothness of the reaction on all values over the compact time
interval is enough for parabolic ODE comparison: compactness supplies a common
range for `u` and `φ`, and smoothness supplies a Lipschitz bound there. -/
theorem le_ode_solution_of_parabolic_inequality_of_smooth_reaction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
    {g : ℝ → RiemannianMetric I M}
    {X : ℝ → SmoothVectorField I M}
    {u ut : M → ℝ → ℝ} {φ φ' : ℝ → ℝ}
    {F : ℝ → ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T)
    (hcont : ContinuousOn (fun z : M × ℝ => u z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hspace : ∀ t ∈ Icc 0 T,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ fun x => u x t)
    (huderiv : ∀ x t, t ∈ Icc 0 T →
      HasDerivWithinAt (u x) (ut x t) (Icc 0 T) t)
    (hφderiv : ∀ t, t ∈ Icc 0 T →
      HasDerivWithinAt φ (φ' t) (Icc 0 T) t)
    (hode : ∀ t ∈ Icc 0 T, φ' t = F (φ t) t)
    (hF : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => F z.1 z.2)
      ((Set.univ : Set ℝ) ×ˢ Icc 0 T))
    (hpde : ∀ t ∈ Icc 0 T, ∀ x,
      ut x t ≤ metricLaplacianAt (g t) (fun y => u y t) x
        + (X t).dir (fun y => u y t) x + F (u x t) t)
    (hzero : ∀ x, u x 0 ≤ φ 0) :
    ∀ x t, t ∈ Icc 0 T → u x t ≤ φ t := by
  have hφcont : ContinuousOn φ (Icc 0 T) :=
    fun t ht => (hφderiv t ht).continuousWithinAt
  obtain ⟨a, b, hu_range, hφ_range⟩ :=
    exists_common_value_interval hT hcont hφcont
  apply le_ode_solution_of_parabolic_inequality_of_contDiffOn
    hT hcont hspace huderiv hφderiv hode ?_ hu_range hφ_range hpde hzero
  exact hF.mono fun z hz => ⟨mem_univ z.1, hz.2⟩

/-- **Math.** Smooth-reaction parabolic comparison when the differential
inequality is available only at strictly positive times. Compactness supplies
the same one-sided reaction bound as in the closed-interval theorem. -/
theorem le_ode_solution_of_parabolic_inequality_of_smooth_reaction_of_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
    {g : ℝ → RiemannianMetric I M}
    {X : ℝ → SmoothVectorField I M}
    {u ut : M → ℝ → ℝ} {φ φ' : ℝ → ℝ}
    {F : ℝ → ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T)
    (hcont : ContinuousOn (fun z : M × ℝ => u z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hspace : ∀ t ∈ Icc 0 T,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ fun x => u x t)
    (huderiv : ∀ x t, t ∈ Icc 0 T →
      HasDerivWithinAt (u x) (ut x t) (Icc 0 T) t)
    (hφderiv : ∀ t, t ∈ Icc 0 T →
      HasDerivWithinAt φ (φ' t) (Icc 0 T) t)
    (hode : ∀ t ∈ Icc 0 T, φ' t = F (φ t) t)
    (hF : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => F z.1 z.2)
      ((Set.univ : Set ℝ) ×ˢ Icc 0 T))
    (hpde : ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      ut x t ≤ metricLaplacianAt (g t) (fun y => u y t) x
        + (X t).dir (fun y => u y t) x + F (u x t) t)
    (hzero : ∀ x, u x 0 ≤ φ 0) :
    ∀ x t, t ∈ Icc 0 T → u x t ≤ φ t := by
  have hφcont : ContinuousOn φ (Icc 0 T) :=
    fun t ht => (hφderiv t ht).continuousWithinAt
  obtain ⟨a, b, hu_range, hφ_range⟩ :=
    exists_common_value_interval hT hcont hφcont
  have hF' : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => F z.1 z.2)
      (Icc a b ×ˢ Icc 0 T) :=
    hF.mono fun z hz => ⟨mem_univ z.1, hz.2⟩
  obtain ⟨K, _hK, hreaction⟩ :=
    exists_nonneg_reaction_bound_on_rectangle hF'
  apply le_ode_solution_of_parabolic_inequality_of_pos
    (K := K) hT hcont hspace huderiv hφderiv hode hpde ?_ hzero
  intro t ht x hφu
  exact hreaction t ht (u x t) (hu_range x t ht)
    (φ t) (hφ_range t ht) hφu.le

/-- **Math.** Weak maximum principle on a closed manifold when the parabolic
inequality is required only at strictly positive times. This is sufficient
because a first positive maximum is never attained at the initial endpoint. -/
theorem weak_maximum_principle_of_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    {g : ℝ → RiemannianMetric I M}
    {X : ℝ → SmoothVectorField I M}
    {u : M → ℝ → ℝ} {φ : ℝ → ℝ}
    {F : ℝ → ℝ → ℝ} {T α : ℝ}
    (hT : 0 < T)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => F z.1 z.2)
      ((Set.univ : Set ℝ) ×ˢ Icc 0 T))
    (hu : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => u z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hpde : ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      derivWithin (u x) (Icc 0 T) t ≤
        metricLaplacianAt (g t) (fun y => u y t) x
          + (X t).dir (fun y => u y t) x + F (u x t) t)
    (hφ : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt φ (F (φ t) t) (Icc 0 T) t)
    (hφzero : φ 0 = α)
    (hzero : ∀ x, u x 0 ≤ α) :
    ∀ x t, t ∈ Icc 0 T → u x t ≤ φ t := by
  cases isEmpty_or_nonempty M with
  | inl hM =>
      intro x
      exact (hM.false x).elim
  | inr hM =>
      letI : Nonempty M := hM
      have huderiv : ∀ x t, t ∈ Icc 0 T →
          HasDerivWithinAt (u x) (derivWithin (u x) (Icc 0 T) t)
            (Icc 0 T) t := by
        intro x t ht
        exact ((contDiffOn_time_slice_of_contMDiffOn_spacetime hu x t ht).differentiableWithinAt
          (by norm_num)).hasDerivWithinAt
      apply le_ode_solution_of_parabolic_inequality_of_smooth_reaction_of_pos
        (ut := fun x t => derivWithin (u x) (Icc 0 T) t)
        (φ' := fun t => F (φ t) t)
        hT.le hu.continuousOn
        (fun t ht => contMDiff_spatial_slice_of_contMDiffOn_spacetime hu ht)
        huderiv hφ (fun _t _ht => rfl) (hF.of_le (by norm_num)) hpde
      intro x
      calc
        u x 0 ≤ α := hzero x
        _ = φ 0 := hφzero.symm

/-- **Math.** Weak maximum principle for a scalar parabolic inequality on a
closed manifold. A solution of the associated reaction ODE bounds the PDE
solution for the whole closed time interval. -/
theorem weak_maximum_principle
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    {g : ℝ → RiemannianMetric I M}
    {X : ℝ → SmoothVectorField I M}
    {u : M → ℝ → ℝ} {φ : ℝ → ℝ}
    {F : ℝ → ℝ → ℝ} {T α : ℝ}
    (hT : 0 < T)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => F z.1 z.2)
      ((Set.univ : Set ℝ) ×ˢ Icc 0 T))
    (hu : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => u z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hpde : ∀ t ∈ Icc 0 T, ∀ x,
      derivWithin (u x) (Icc 0 T) t ≤
        metricLaplacianAt (g t) (fun y => u y t) x
          + (X t).dir (fun y => u y t) x + F (u x t) t)
    (hφ : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt φ (F (φ t) t) (Icc 0 T) t)
    (hφzero : φ 0 = α)
    (hzero : ∀ x, u x 0 ≤ α) :
    ∀ x t, t ∈ Icc 0 T → u x t ≤ φ t := by
  cases isEmpty_or_nonempty M with
  | inl hM =>
      intro x
      exact (hM.false x).elim
  | inr hM =>
      letI : Nonempty M := hM
      have huderiv : ∀ x t, t ∈ Icc 0 T →
          HasDerivWithinAt (u x) (derivWithin (u x) (Icc 0 T) t)
            (Icc 0 T) t := by
        intro x t ht
        exact ((contDiffOn_time_slice_of_contMDiffOn_spacetime hu x t ht).differentiableWithinAt
          (by norm_num)).hasDerivWithinAt
      apply le_ode_solution_of_parabolic_inequality_of_smooth_reaction
        (ut := fun x t => derivWithin (u x) (Icc 0 T) t)
        (φ' := fun t => F (φ t) t)
        hT.le hu.continuousOn
        (fun t ht => contMDiff_spatial_slice_of_contMDiffOn_spacetime hu ht)
        huderiv hφ (fun _t _ht => rfl) (hF.of_le (by norm_num)) hpde
      intro x
      calc
        u x 0 ≤ α := hzero x
        _ = φ 0 := hφzero.symm

/-- **Math.** Weak minimum principle with the parabolic inequality required
only at strictly positive times, obtained by the same sign duality. -/
theorem weak_minimum_principle_of_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    {g : ℝ → RiemannianMetric I M}
    {X : ℝ → SmoothVectorField I M}
    {u : M → ℝ → ℝ} {φ : ℝ → ℝ}
    {F : ℝ → ℝ → ℝ} {T α : ℝ}
    (hT : 0 < T)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => F z.1 z.2)
      ((Set.univ : Set ℝ) ×ˢ Icc 0 T))
    (hu : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => u z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hpde : ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      metricLaplacianAt (g t) (fun y => u y t) x
          + (X t).dir (fun y => u y t) x + F (u x t) t ≤
        derivWithin (u x) (Icc 0 T) t)
    (hφ : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt φ (F (φ t) t) (Icc 0 T) t)
    (hφzero : φ 0 = α)
    (hzero : ∀ x, α ≤ u x 0) :
    ∀ x t, t ∈ Icc 0 T → φ t ≤ u x t := by
  let v : M → ℝ → ℝ := fun x t => -u x t
  let G : ℝ → ℝ → ℝ := fun s t => -F (-s) t
  have hflip : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (-z.1, z.2)) :=
    contDiff_fst.neg.prodMk contDiff_snd
  have hGcomp : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => F (-z.1) z.2)
      ((Set.univ : Set ℝ) ×ˢ Icc 0 T) := by
    simpa [Function.comp_def] using
      hF.comp hflip.contDiffOn
        (fun z hz => ⟨mem_univ (-z.1), hz.2⟩)
  have hG : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => G z.1 z.2)
      ((Set.univ : Set ℝ) ×ˢ Icc 0 T) := by
    simpa [G] using hGcomp.neg
  have hv : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => v z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T) := by
    simpa [v] using hu.neg
  have hψ : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (-φ) (G ((-φ) t) t) (Icc 0 T) t := by
    intro t ht
    simpa only [G, Pi.neg_apply, neg_neg] using (hφ t ht).neg
  have hvpde : ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      derivWithin (v x) (Icc 0 T) t ≤
        metricLaplacianAt (g t) (fun y => v y t) x
          + (X t).dir (fun y => v y t) x + G (v x t) t := by
    intro t ht htpos x
    have hdu : derivWithin (fun s => -u x s) (Icc 0 T) t =
        -derivWithin (u x) (Icc 0 T) t := by
      exact derivWithin.neg
    have hdir : (X t).dir (fun y => -u y t) x =
        -(X t).dir (fun y => u y t) x := by
      simp only [SmoothVectorField.dir]
      rw [show (fun y => -u y t) = -(fun y => u y t) by rfl, mfderiv_neg]
      rfl
    dsimp [v, G]
    rw [hdu, metricLaplacianAt_neg, hdir]
    simp only [neg_neg]
    linarith [hpde t ht htpos x]
  have hcomparison := weak_maximum_principle_of_pos
    (g := g) (X := X) (u := v) (φ := -φ) (F := G) (T := T) (α := -α)
    hT hG hv hvpde hψ (by simp [hφzero])
    (fun x => by dsimp [v]; linarith [hzero x])
  intro x t ht
  have h := hcomparison x t ht
  dsimp [v] at h
  linarith

/-- **Math.** Weak minimum principle for a scalar parabolic inequality on a
closed manifold, obtained from the weak maximum principle by sign duality. -/
theorem weak_minimum_principle
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    {g : ℝ → RiemannianMetric I M}
    {X : ℝ → SmoothVectorField I M}
    {u : M → ℝ → ℝ} {φ : ℝ → ℝ}
    {F : ℝ → ℝ → ℝ} {T α : ℝ}
    (hT : 0 < T)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => F z.1 z.2)
      ((Set.univ : Set ℝ) ×ˢ Icc 0 T))
    (hu : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => u z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hpde : ∀ t ∈ Icc 0 T, ∀ x,
      metricLaplacianAt (g t) (fun y => u y t) x
          + (X t).dir (fun y => u y t) x + F (u x t) t ≤
        derivWithin (u x) (Icc 0 T) t)
    (hφ : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt φ (F (φ t) t) (Icc 0 T) t)
    (hφzero : φ 0 = α)
    (hzero : ∀ x, α ≤ u x 0) :
    ∀ x t, t ∈ Icc 0 T → φ t ≤ u x t := by
  let v : M → ℝ → ℝ := fun x t => -u x t
  let G : ℝ → ℝ → ℝ := fun s t => -F (-s) t
  have hflip : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (-z.1, z.2)) :=
    contDiff_fst.neg.prodMk contDiff_snd
  have hGcomp : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => F (-z.1) z.2)
      ((Set.univ : Set ℝ) ×ˢ Icc 0 T) := by
    simpa [Function.comp_def] using
      hF.comp hflip.contDiffOn
        (fun z hz => ⟨mem_univ (-z.1), hz.2⟩)
  have hG : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => G z.1 z.2)
      ((Set.univ : Set ℝ) ×ˢ Icc 0 T) := by
    simpa [G] using hGcomp.neg
  have hv : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => v z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T) := by
    simpa [v] using hu.neg
  have hψ : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (-φ) (G ((-φ) t) t) (Icc 0 T) t := by
    intro t ht
    simpa only [G, Pi.neg_apply, neg_neg] using (hφ t ht).neg
  have hvpde : ∀ t ∈ Icc 0 T, ∀ x,
      derivWithin (v x) (Icc 0 T) t ≤
        metricLaplacianAt (g t) (fun y => v y t) x
          + (X t).dir (fun y => v y t) x + G (v x t) t := by
    intro t ht x
    have hdu : derivWithin (fun s => -u x s) (Icc 0 T) t =
        -derivWithin (u x) (Icc 0 T) t := by
      exact derivWithin.neg
    have hdir : (X t).dir (fun y => -u y t) x =
        -(X t).dir (fun y => u y t) x := by
      simp only [SmoothVectorField.dir]
      rw [show (fun y => -u y t) = -(fun y => u y t) by rfl, mfderiv_neg]
      rfl
    dsimp [v, G]
    rw [hdu, metricLaplacianAt_neg, hdir]
    simp only [neg_neg]
    linarith [hpde t ht x]
  have hcomparison := weak_maximum_principle
    (g := g) (X := X) (u := v) (φ := -φ) (F := G) (T := T) (α := -α)
    hT hG hv hvpde hψ (by simp [hφzero])
    (fun x => by dsimp [v]; linarith [hzero x])
  intro x t ht
  have h := hcomparison x t ht
  dsimp [v] at h
  linarith

end Topping
