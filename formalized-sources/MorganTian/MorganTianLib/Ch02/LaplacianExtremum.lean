import MorganTianLib.Ch02.Laplacian
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Morgan–Tian Ch. 2 §2.2 — the Laplacian at an interior maximum

Blueprint `lem:laplacian-nonpositive-at-max`: if a smooth function `v` on an
open set `U` of a Riemannian manifold has a local maximum at `q ∈ U`, then
`dv(q) = 0` and `Δv(q) ≤ 0`.

Rather than expanding `Δ` in a coordinate chart as the blueprint proof does,
we prove the two statements invariantly, by restricting `f` to integral curves:

* for a tangent vector `v ∈ T_qM`, extend it to a global smooth field `X`
  (`extendVector`) and let `γ` be an integral curve of `X` through `q`
  (Mathlib, `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`); then
  `t ↦ f(γ(t))` has a local maximum at `0`, and its first two derivatives at
  `0` are `df_q(v)` and — once `df_q = 0` kills the connection term —
  `Hess(f)_q(v,v)` (`eventually_hasDerivAt_comp_of_isMIntegralCurveAt`);
* the vanishing of the first derivative at a local maximum
  (`mfderiv_eq_zero_of_isLocalMax`, the manifold Fermat lemma — not in
  Mathlib) gives `dv(q) = 0`, and the one-dimensional second-derivative test
  (`deriv_deriv_nonpos_of_isLocalMax`, the converse direction of Mathlib's
  `isLocalMin_of_deriv_deriv_pos`) gives `Hess(f)_q(v,v) ≤ 0`
  (`hessianAt_nonpos_of_isLocalMax`);
* summing over an orthonormal basis of `(T_qM, g_q)` gives `Δf(q) ≤ 0`
  (`laplacianAt_nonpos_of_isLocalMax`). This is the trace step
  `Tr(AH) = Σ_k λ_k u_k^T H u_k ≤ 0` of the blueprint proof, with the
  diagonalization absorbed into the orthonormal-basis formulation of the
  trace.

The chart formulation and the invariant formulation of the statement agree
because both compute `Δ` as the `g`-trace of the second-order jet of `f` at a
critical point. The localized version (`f` smooth only on an open set `U`)
is `laplacianAt_nonpos_of_isLocalMaxOn`, obtained from the global one by
gluing `f` with a smooth bump function.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 2 §2.2
(blueprint `lem:laplacian-nonpositive-at-max`).
-/

open scoped ContDiff Manifold Topology Bundle
open Riemannian Filter

noncomputable section

namespace MorganTianLib

/-! ### One-dimensional lemmas -/

/-- **Math.** Converse second-derivative test: at a local maximum `t₀` of a
continuous `φ : ℝ → ℝ` with `φ'(t₀) = 0`, the (junk-robust) second derivative
satisfies `φ''(t₀) ≤ 0`. Indeed if `φ''(t₀) > 0` then `t₀` is also a local
minimum (`isLocalMin_of_deriv_deriv_pos`), so `φ` is constant near `t₀`,
forcing `φ''(t₀) = 0`. Blueprint: `lem:laplacian-nonpositive-at-max` (the
one-variable second-derivative statement). -/
theorem deriv_deriv_nonpos_of_isLocalMax {φ : ℝ → ℝ} {t₀ : ℝ}
    (hmax : IsLocalMax φ t₀) (hc : ContinuousAt φ t₀) :
    deriv (deriv φ) t₀ ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have hd : deriv φ t₀ = 0 := hmax.deriv_eq_zero
  have hmin : IsLocalMin φ t₀ := isLocalMin_of_deriv_deriv_pos hpos hd hc
  have hconst : ∀ᶠ t in 𝓝 t₀, φ t = φ t₀ := by
    filter_upwards [hmax, hmin] with t h₁ h₂
    exact le_antisymm h₁ h₂
  have hderiv0 : deriv φ =ᶠ[𝓝 t₀] fun _ => (0 : ℝ) := by
    filter_upwards [hconst.eventually_nhds] with t ht
    have : deriv φ t = deriv (fun _ => φ t₀) t := Filter.EventuallyEq.deriv_eq ht
    simpa using this
  have h0 : deriv (deriv φ) t₀ = 0 := by
    rw [Filter.EventuallyEq.deriv_eq hderiv0]
    simp
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Differentiating a function along an integral curve -/

omit [CompleteSpace E] in
/-- **Math.** Chain rule along an integral curve: if `γ` is an integral curve
of the smooth field `X` near `t₀` and `F : M → ℝ` is smooth, then near `t₀`
the composite `F ∘ γ` is differentiable with derivative `X(F)(γ(t))`, the
directional derivative of `F` along `X`.
Blueprint: `lem:laplacian-nonpositive-at-max` (restriction to curves). -/
theorem eventually_hasDerivAt_comp_of_isMIntegralCurveAt
    {X : SmoothVectorField I M} {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsMIntegralCurveAt γ X.toFun t₀) {F : M → ℝ}
    (hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ F) :
    ∀ᶠ t in 𝓝 t₀, HasDerivAt (F ∘ γ) (X.dir F (γ t)) t := by
  filter_upwards [hγ] with t ht
  have hFd : HasMFDerivAt I 𝓘(ℝ, ℝ) F (γ t) (mfderiv I 𝓘(ℝ, ℝ) F (γ t)) :=
    ((hF (γ t)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hcomp := hFd.comp t ht
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply hcomp.congr_mfderiv
  ext
  exact (congrArg (mfderiv I 𝓘(ℝ, ℝ) F (γ t))
    (one_smul ℝ (X.toFun (γ t)))).trans (one_smul ℝ _).symm

variable [I.Boundaryless]

/-- **Math.** Integral curve through a point: every smooth vector field `X` on
a boundaryless manifold admits an integral curve `γ` with `γ 0 = q`.
Specialization of Mathlib's Picard–Lindelöf-based
`exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless` to
`SmoothVectorField`. Blueprint: `lem:laplacian-nonpositive-at-max`. -/
theorem exists_isMIntegralCurveAt_smoothVectorField (X : SmoothVectorField I M)
    (q : M) : ∃ γ : ℝ → M, γ 0 = q ∧ IsMIntegralCurveAt γ X.toFun 0 :=
  exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless 0
    ((X.smooth q).of_le (by norm_num))

/-! ### The manifold Fermat lemma -/

omit [CompleteSpace E] in
/-- **Math.** **Fermat's lemma on a manifold**: at a local maximum `q` of a
smooth function `f : M → ℝ`, the differential vanishes: `df_q = 0`. Proof:
for `v ∈ T_qM`, restrict `f` to an integral curve `γ` of a smooth field
through `v`; then `f ∘ γ` has a local maximum at `0` and derivative
`df_q(v)` there, so `df_q(v) = 0` by the one-variable Fermat lemma.
Blueprint: `lem:laplacian-nonpositive-at-max` (first assertion). -/
theorem mfderiv_eq_zero_of_isLocalMax [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {q : M} (hmax : IsLocalMax f q) :
    mfderiv I 𝓘(ℝ, ℝ) f q = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  set X := extendVector q v with hX
  obtain ⟨γ, hγ0, hγ⟩ := exists_isMIntegralCurveAt_smoothVectorField X q
  have hev := eventually_hasDerivAt_comp_of_isMIntegralCurveAt hγ hf
  have h0 : HasDerivAt (f ∘ γ) (X.dir f (γ 0)) 0 := hev.self_of_nhds
  have hcont : ContinuousAt γ 0 := hγ.hasMFDerivAt.continuousAt
  have hmax' : IsLocalMax (f ∘ γ) 0 := by
    have htend : Filter.Tendsto γ (𝓝 0) (𝓝 q) := hγ0 ▸ hcont.tendsto
    have hev' : ∀ᶠ t in 𝓝 (0 : ℝ), f (γ t) ≤ f q := htend.eventually hmax
    filter_upwards [hev'] with t ht
    simpa [Function.comp, hγ0] using ht
  have hzero : X.dir f (γ 0) = 0 := hmax'.hasDerivAt_eq_zero h0
  rw [hγ0] at hzero
  simpa [SmoothVectorField.dir, hX] using hzero

/-! ### The Laplacian at an interior maximum -/

omit [CompleteSpace E] in
/-- **Math.** At a local maximum `q` of a smooth function `f`, the Hessian is
negative semi-definite: `Hess(f)_q(v, v) ≤ 0` for every `v ∈ T_qM`. Proof: by
Fermat's lemma the connection term of the Hessian dies at `q`, so
`Hess(f)_q(v,v) = X(X(f))(q)` for an extension `X` of `v`, which is the second
derivative at `0` of `f` restricted to an integral curve of `X` — nonpositive
at a local maximum by the converse second-derivative test.
Blueprint: `lem:laplacian-nonpositive-at-max` (the matrix `H` is negative
semi-definite). -/
theorem hessianAt_nonpos_of_isLocalMax [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] (nabla : AffineConnection I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {q : M} (hmax : IsLocalMax f q)
    (v : TangentSpace I q) : hessianAt nabla f q v v ≤ 0 := by
  have hcrit : mfderiv I 𝓘(ℝ, ℝ) f q = 0 := mfderiv_eq_zero_of_isLocalMax hf hmax
  set X := extendVector q v with hX
  -- the connection term of the Hessian vanishes at the critical point
  have hsecond : (nabla.cov X X).dir f q = 0 := by
    simp only [SmoothVectorField.dir, hcrit, ContinuousLinearMap.zero_apply]
  -- restrict to an integral curve of `X` through `q`
  obtain ⟨γ, hγ0, hγ⟩ := exists_isMIntegralCurveAt_smoothVectorField X q
  have hφev : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (f ∘ γ) (X.dir f (γ t)) t :=
    eventually_hasDerivAt_comp_of_isMIntegralCurveAt hγ hf
  have hφ' : deriv (f ∘ γ) =ᶠ[𝓝 (0 : ℝ)] (X.dir f) ∘ γ := by
    filter_upwards [hφev] with t ht
    exact ht.deriv
  have hdirf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (X.dir f) := X.dir_contMDiff hf
  have h2 : HasDerivAt ((X.dir f) ∘ γ) (X.dir (X.dir f) (γ 0)) 0 :=
    (eventually_hasDerivAt_comp_of_isMIntegralCurveAt hγ hdirf).self_of_nhds
  -- the second derivative of `f ∘ γ` at `0` is `X(X(f))(q)`
  have hdd : deriv (deriv (f ∘ γ)) 0 = X.dir (X.dir f) q := by
    rw [Filter.EventuallyEq.deriv_eq hφ', h2.deriv, hγ0]
  -- `f ∘ γ` has a local maximum at `0`
  have hcont : ContinuousAt γ 0 := hγ.hasMFDerivAt.continuousAt
  have hmax' : IsLocalMax (f ∘ γ) 0 := by
    have htend : Filter.Tendsto γ (𝓝 0) (𝓝 q) := hγ0 ▸ hcont.tendsto
    have hev' : ∀ᶠ t in 𝓝 (0 : ℝ), f (γ t) ≤ f q := htend.eventually hmax
    filter_upwards [hev'] with t ht
    simpa [Function.comp, hγ0] using ht
  have hφcont : ContinuousAt (f ∘ γ) 0 :=
    ((hf (γ 0)).continuousAt).comp hcont
  -- conclude by the converse second-derivative test
  have hnonpos : deriv (deriv (f ∘ γ)) 0 ≤ 0 :=
    deriv_deriv_nonpos_of_isLocalMax hmax' hφcont
  have : hessianAt nabla f q v v = X.dir (X.dir f) q - (nabla.cov X X).dir f q := rfl
  rw [this, hsecond, sub_zero, ← hdd]
  exact hnonpos

omit [CompleteSpace E] in
/-- **Math.** **The Laplacian is non-positive at an interior maximum** (global
form): if a smooth function `f : M → ℝ` on a Riemannian manifold has a local
maximum at `q`, then `df_q = 0` and `Δf(q) ≤ 0`. The Laplacian is the
`g`-trace of the Hessian, a diagonal sum of the nonpositive values
`Hess(f)_q(eᵢ, eᵢ)` over an orthonormal basis — the blueprint's
`Tr(AH) = Σ_k λ_k u_k^THu_k ≤ 0`.
Blueprint: `lem:laplacian-nonpositive-at-max`. -/
theorem laplacianAt_nonpos_of_isLocalMax [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {q : M} (hmax : IsLocalMax f q) :
    mfderiv I 𝓘(ℝ, ℝ) f q = 0 ∧ laplacianAt g nabla f q ≤ 0 := by
  refine ⟨mfderiv_eq_zero_of_isLocalMax hf hmax, ?_⟩
  unfold laplacianAt
  exact Finset.sum_nonpos fun i _ =>
    hessianAt_nonpos_of_isLocalMax nabla hf hmax _

/-! ### Localization: functions smooth only on an open set -/

omit [I.Boundaryless] [CompleteSpace E] in
/-- **Math.** A function smooth on an open set `U ∋ q` agrees near `q` with a
globally smooth function: multiply by a smooth bump function at `q` supported
in `U`. Blueprint: `lem:laplacian-nonpositive-at-max` (localization). -/
theorem exists_contMDiff_eventuallyEq_of_contMDiffOn [FiniteDimensional ℝ E]
    [T2Space M] {U : Set M} (hU : IsOpen U) {q : M} (hq : q ∈ U) {f : M → ℝ}
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) :
    ∃ f' : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f' ∧ f' =ᶠ[𝓝 q] f := by
  obtain ⟨χ, -, hχU⟩ :=
    ((SmoothBumpFunction.nhds_basis_tsupport (I := I) q).mem_iff).mp
      (hU.mem_nhds hq)
  refine ⟨fun x => χ x • f x, ?_, ?_⟩
  · refine contMDiff_of_tsupport fun x hx => ?_
    have hxU : x ∈ U := hχU (tsupport_smul_subset_left (fun y => χ y) f hx)
    exact χ.contMDiffAt.smul (hf.contMDiffAt (hU.mem_nhds hxU))
  · filter_upwards [χ.eventuallyEq_one] with x hx
    simp [hx]

omit [CompleteSpace E] in
/-- **Math.** **The Laplacian is non-positive at an interior maximum**
(Morgan–Tian, Ch. 2 §2.2). Let `U ⊆ M` be open and let `v` be a smooth
function on `U`. If `q ∈ U` is a local maximum of `v`, then `dv(q) = 0` and
`Δv(q) ≤ 0`. Stated for `f : M → ℝ` smooth on `U` with a local maximum along
`U` at `q`; both conclusions only see the germ of `f` at `q ∈ U`, so the
statement is exactly the blueprint's. Proved from the global version by
gluing `f` with a smooth bump function at `q` supported in `U`.
Blueprint: `lem:laplacian-nonpositive-at-max`. -/
theorem laplacianAt_nonpos_of_isLocalMaxOn [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) {U : Set M} (hU : IsOpen U) {f : M → ℝ}
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) {q : M} (hq : q ∈ U)
    (hmax : IsLocalMaxOn f U q) :
    mfderiv I 𝓘(ℝ, ℝ) f q = 0 ∧ laplacianAt g nabla f q ≤ 0 := by
  obtain ⟨f', hf', hff'⟩ := exists_contMDiff_eventuallyEq_of_contMDiffOn hU hq hf
  have hUq : U ∈ 𝓝 q := hU.mem_nhds hq
  have hmaxq : ∀ᶠ x in 𝓝 q, f x ≤ f q := by
    have h := hmax
    rwa [IsLocalMaxOn, IsMaxFilter, nhdsWithin_eq_nhds.mpr hUq] at h
  have hfq : f' q = f q := hff'.eq_of_nhds
  have hmax' : IsLocalMax f' q := by
    filter_upwards [hmaxq, hff'] with x hx hfx
    rw [hfx, hfq]
    exact hx
  obtain ⟨h1, h2⟩ := laplacianAt_nonpos_of_isLocalMax g nabla hf' hmax'
  constructor
  · rw [← Filter.EventuallyEq.mfderiv_eq hff']
    exact h1
  · rw [← laplacianAt_congr_of_eventuallyEq g nabla hff']
    exact h2

end MorganTianLib

end
