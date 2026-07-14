import PetersenLib.Ch01.TensorConcepts
import PetersenLib.Ch01.ArcLength
import PetersenLib.Ch01.Sphere
import PetersenLib.Ch01.HyperbolicSpace
import PetersenLib.Ch01.HopfFibration
import PetersenLib.Ch01.SphereRadialProjection
import PetersenLib.Ch01.NoFlatImmersion
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Petersen Ch. 1, §1.6 — Exercises 1.6.11–1.6.21

The tensor-algebra exercises 1.6.11–1.6.14 (formalized against
`PetersenLib.Ch01.TensorConcepts`), the projective-quotient exercise 1.6.15,
and the arc-length exercises 1.6.16–1.6.21 (formalized against
`PetersenLib.Ch01.ArcLength`):

* **Exercise 1.6.11** (`exercise1_6_11`, `dualMetric`): type change is a
  contraction of a tensor product with `g` or `g⁻¹`.
* **Exercise 1.6.12** (`exercise1_6_12`): `|T|² = ∑ |T(E_i)|²` in an
  orthonormal basis.
* **Exercise 1.6.13** (`exercise1_6_13`): symmetric and skew-symmetric
  `(1,1)`-tensors are orthogonal.
* **Exercise 1.6.14** (`exercise1_6_14`): the inner product of two tensors of
  the same type is a sequence of type changes of one tensor followed by
  contractions.
* **Exercise 1.6.15** (`exercise1_6_15`,
  `not_riemannianSubmersion_of_smul_invariant`, `hopfQuotientMap`): the
  quotient map `𝔽^{n+1} − {0} → 𝔽Pⁿ`.
* **Exercise 1.6.16** (`exercise1_6_16`): invariance of arc length under
  reparametrization, and unit-speed reparametrization.
* **Exercise 1.6.17** (`exercise1_6_17`): Riemannian immersions preserve arc
  length.
* **Exercise 1.6.18** (`exercise1_6_18`): `L(F ∘ c) ≤ L(c)` under a
  Riemannian submersion, with equality iff `ċ ⊥ ker DF` throughout.
* **Exercise 1.6.19** (`exercise1_6_19`): straight lines minimize length in
  Euclidean space.
* **Exercise 1.6.20** (`exercise1_6_20`): great circles minimize on the
  sphere.
* **Exercise 1.6.21** (`exercise1_6_21`): hyperbolas minimize on hyperbolic
  space.

## Design notes / formalization choices

* **1.6.15.** Mathlib has no smooth-manifold structure on projective spaces,
  so (following the hypothesis-representation pattern of
  `PetersenLib.quotientMetric`) part (2) is proved *abstractly*: for **any**
  smooth structure/metrization of the target and **any** map invariant under
  the scalar action (`F(cx) = F(x)`), the submersion-isometry conditions on
  the punctured space are contradictory
  (`not_riemannianSubmersion_of_smul_invariant`) — no metric on the target
  makes `F` a Riemannian submersion for the standard flat metric. Parts (1)
  and (3) are *instantiated* at the one projective space the library
  realizes: `ℂP¹ = S²(1/2)` via the Hopf fibration (`hopfQuotientMap`,
  extending `hopfMap` by radial projection). The punctured domain
  `𝔽^{n+1} − {0}` is handled by restricting every condition to `x ≠ 0`
  (all conditions are local, and `{x ≠ 0}` is open), avoiding
  open-submanifold bookkeeping. The metric of part (3) is a smooth family of
  inner products on the punctured space, which on an open subset of a vector
  space is exactly the data of a Riemannian metric.
* **1.6.16.** Parts (1) and (2) are formalized (part (1) is
  `arcLength_reparam`; part (2) produces the inverse `φ` of the arc-length
  function `t ↦ L(c)|_a^t` via the 1-dimensional inverse function theorem).
  Part (3) — extension of arc length to absolutely continuous curves — is
  **not formalized**: Mathlib currently has no theory of absolutely
  continuous functions, so there is no infrastructure to state it against.
* **1.6.18.** The pointwise inequality `|DF(v)| ≤ |v|` and its equality case
  come from decomposing `v` against `ker DF` with respect to the
  `g_M`-orthogonality (via `LinearMap.BilinForm.orthogonal`, since the fibre
  metric is not an `InnerProductSpace` instance). The equality case of the
  integrated statement needs `a < b` (over a degenerate interval the integral
  identity is vacuous).
* **1.6.20 / 1.6.21.** Stated in the ambient space: a curve on `Sⁿ ⊂ ℝⁿ⁺¹`
  (resp. `Hⁿ ⊂ ℝ^{n,1}`) is a curve `c : ℝ → E` with `‖c t‖ = 1` (resp.
  `η(c t, c t) = -1`, `0 < (c t)_t`), and its length in the induced metric is
  the ambient integral `∫ ‖ċ‖` (resp. `∫ √η(ċ, ċ)`) — this is Exercise
  1.6.17 for the isometric embeddings `sphereMetric_isRiemannianImmersion` /
  `hyperbolicSpace`. All five parts are proved. The no-immersion parts (5)
  do *not* follow Petersen's angle-comparison hint (which would need the
  images of straight segments to be geodesics of the target — Chapter 5
  material); they are instances of the Chapter-1 second-order obstruction
  `no_isometricImmersion_flat_to_umbilic` (`PetersenLib.Ch01.NoFlatImmersion`).
  Since a Riemannian immersion is by definition a *smooth* map, part (5)
  hypothesizes `ContMDiffAt … ∞` for `F`: a merely once-differentiable map
  carries no second-order information, and the obstruction is second-order.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.6, Exercises
1.6.11–1.6.21.
-/

open Bundle Metric Module Set
open scoped ContDiff Manifold Topology InnerProductSpace

noncomputable section

namespace PetersenLib

/-! ## Exercises 1.6.11–1.6.14 — tensor algebra -/

section TensorExercises

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

variable (V) in
/-- **Math.** Petersen §1.6, Exercise 1.6.11: the `(2,0)`-tensor `g⁻¹`, the
**inner product on the dual space** `T_p^*M`, obtained from the metric by
raising both indices: `g⁻¹(φ, ψ) = g(♯φ, ♯ψ) = φ(♯ψ)`; in coordinates
`g^{ij} = g(dx^i, dx^j)` is the inverse matrix of `g_{ij}`. -/
def dualMetric : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] (V →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ :=
  twoZeroOfZeroTwo V (innerₗ V)

@[simp]
theorem dualMetric_apply (φ ψ : V →ₗ[ℝ] ℝ) :
    dualMetric V φ ψ
      = ⟪(tensorTypeChange V).symm φ, (tensorTypeChange V).symm ψ⟫_ℝ := by
  rw [dualMetric, twoZeroOfZeroTwo_apply]
  rfl

/-- **Math.** `g⁻¹(φ, ψ) = φ(♯ψ)`: pairing a `1`-form against the vector dual
to the other. -/
theorem dualMetric_apply' (φ ψ : V →ₗ[ℝ] ℝ) :
    dualMetric V φ ψ = φ ((tensorTypeChange V).symm ψ) := by
  rw [dualMetric_apply, inner_tensorTypeChange_symm]

/-- **Math.** **Exercise 1.6.11** (Petersen §1.6): with `g⁻¹` the `(2,0)`-inner
product on `T^*M` (`dualMetric`), **type change is a contraction of a tensor
product with `g` or `g⁻¹`**. In an orthonormal frame `E_i` (so that
`g_{ij} = ⟪E_i, E_j⟫` and `g⁻¹(σ^i, σ^j)` are the metric components):

1. lowering a vector, `(♭v)_j = C(v ⊗ g)_j = v^i g_{ij}`;
2. raising a `1`-form, `(♯φ)^i = C(φ ⊗ g⁻¹)^i = φ_j g^{ji}`;
3. lowering an index of a `(1,1)`-tensor, `(♭T)_{jl} = C(T ⊗ g)_{jl} = T^i_j g_{il}`;
4. raising an index of a `(0,2)`-tensor, `(♯B)^i_u = C(B ⊗ g⁻¹) = B_{uj} g^{ji}`.

Each contraction is displayed as the orthonormal-frame sum over the paired
index, with the tensor's components against `b` contracted against the
components of `g` (an inner product) or of `g⁻¹` (a `dualMetric` value). -/
theorem exercise1_6_11 {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (v : V) (φ : V →ₗ[ℝ] ℝ) (T : V →ₗ[ℝ] V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    (∀ w, tensorTypeChange V v w = ∑ i, ⟪v, b i⟫_ℝ * ⟪b i, w⟫_ℝ) ∧
    (tensorTypeChange V).symm φ
      = ∑ i, dualMetric V φ (tensorTypeChange V (b i)) • b i ∧
    (∀ u w, lowerIndex V T u w = ∑ i, ⟪T u, b i⟫_ℝ * ⟪b i, w⟫_ℝ) ∧
    (∀ u w, ⟪raiseIndex V B u, w⟫_ℝ
      = ∑ i, B u (b i) * dualMetric V (tensorTypeChange V (b i)) (tensorTypeChange V w)) := by
  have hdual_basis : ∀ (ψ : V →ₗ[ℝ] ℝ) (i : ι),
      dualMetric V ψ (tensorTypeChange V (b i)) = ψ (b i) := by
    intro ψ i
    rw [dualMetric_apply' , LinearEquiv.symm_apply_apply]
  refine ⟨fun w => ?_, ?_, fun u w => ?_, fun u w => ?_⟩
  · rw [tensorTypeChange_apply, ← b.sum_inner_mul_inner v w]
  · have : ∀ i, dualMetric V φ (tensorTypeChange V (b i))
        = ⟪b i, (tensorTypeChange V).symm φ⟫_ℝ := by
      intro i
      rw [hdual_basis, real_inner_comm, ← inner_tensorTypeChange_symm φ (b i),
        real_inner_comm]
    simp only [this]
    exact (b.sum_repr' ((tensorTypeChange V).symm φ)).symm
  · rw [lowerIndex_apply, ← b.sum_inner_mul_inner (T u) w]
  · have hcomp : ∀ i, dualMetric V (tensorTypeChange V (b i)) (tensorTypeChange V w)
        = ⟪b i, w⟫_ℝ := by
      intro i
      rw [dualMetric_apply', LinearEquiv.symm_apply_apply, tensorTypeChange_apply]
    simp only [hcomp, inner_raiseIndex]
    calc B u w = B u (∑ i, ⟪b i, w⟫_ℝ • b i) := by rw [b.sum_repr' w]
      _ = ∑ i, B u (b i) * ⟪b i, w⟫_ℝ := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ => by
            rw [map_smul, smul_eq_mul, mul_comm]

/-- **Math.** **Exercise 1.6.12** (Petersen §1.6): for a `(1,1)`-tensor `T` on
a Riemannian manifold and an orthonormal frame `E_i`,
`|T|² = ∑ᵢ |T(E_i)|²` — the Euclidean tensor norm is the sum of the squared
lengths of the images of an orthonormal frame. -/
theorem exercise1_6_12 {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (T : V →ₗ[ℝ] V) :
    euclideanNormLinearMap T ^ 2 = ∑ i, ‖T (b i)‖ ^ 2 := by
  rw [sq_euclideanNormLinearMap, traceInnerProduct_eq_sum_inner b]
  exact Finset.sum_congr rfl fun i _ => real_inner_self_eq_norm_sq _

/-- **Math.** **Exercise 1.6.13** (Petersen §1.6): a symmetric and a
skew-symmetric `(1,1)`-tensor are **orthogonal**, `g(S, T) = 0`.

Proof: the adjoints are `S^* = S` and `T^* = -T`, so
`g(S,T) = tr(T^* S) = -tr(TS)` while by symmetry of the inner product
`g(S,T) = g(T,S) = tr(S^* T) = tr(ST) = tr(TS)`; hence `g(S,T) = 0`. -/
theorem exercise1_6_13 (S T : V →ₗ[ℝ] V)
    (hS : ∀ u w, ⟪S u, w⟫_ℝ = ⟪u, S w⟫_ℝ)
    (hT : ∀ u w, ⟪T u, w⟫_ℝ = -⟪u, T w⟫_ℝ) :
    traceInnerProduct S T = 0 := by
  have hSadj : S = LinearMap.adjoint S := (LinearMap.eq_adjoint_iff S S).mpr hS
  have hTadj : -T = LinearMap.adjoint T := by
    refine (LinearMap.eq_adjoint_iff (-T) T).mpr fun u w => ?_
    rw [LinearMap.neg_apply, inner_neg_left, hT, neg_neg]
  have h1 : traceInnerProduct S T = -(LinearMap.trace ℝ V (T ∘ₗ S)) := by
    rw [traceInnerProduct, ← hTadj, LinearMap.neg_comp, map_neg]
  have h2 : traceInnerProduct S T = LinearMap.trace ℝ V (T ∘ₗ S) := by
    rw [traceInnerProduct_comm, traceInnerProduct, ← hSadj,
      LinearMap.trace_comp_comm']
  linarith [h1, h2]

/-- **Math.** **Exercise 1.6.14** (Petersen §1.6): **the inner product of two
tensors of the same type is a sequence of type changes applied to one of them
followed by contractions.**

* For `(1,1)`-tensors: `g(T₁, T₂) = tr(T₂^* ∘ T₁)`, where the adjoint
  `T₂^* = ♯((♭T₂)ᵗ)` is obtained from `T₂` by lowering its index, transposing
  the two lower slots (a positional change, §1.5.4), and raising the other
  index; composition with `T₁` contracts one index pair and the final trace
  (`tensorContraction ∘ lowerIndex`, §1.5.2) contracts the other.
* For `(0,2)`-tensors: the same computation after first raising an index of
  each factor, `g(B₁, B₂) = tr(♯(B₂ᵗ) ∘ ♯B₁)`. -/
theorem exercise1_6_14 (T₁ T₂ : V →ₗ[ℝ] V) (B₁ B₂ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    traceInnerProduct T₁ T₂
      = tensorContraction V
          (lowerIndex V (raiseIndex V ((lowerIndex V T₂).flip) ∘ₗ T₁)) ∧
    pointwiseTensorInnerProduct B₁ B₂
      = tensorContraction V
          (lowerIndex V (raiseIndex V B₂.flip ∘ₗ raiseIndex V B₁)) := by
  have hadj : ∀ T : V →ₗ[ℝ] V,
      raiseIndex V ((lowerIndex V T).flip) = LinearMap.adjoint T := by
    intro T
    refine LinearMap.ext fun u => ext_inner_right ℝ fun w => ?_
    rw [inner_raiseIndex, LinearMap.flip_apply, lowerIndex_apply,
      LinearMap.adjoint_inner_left, real_inner_comm]
  constructor
  · rw [tensorContraction_lowerIndex, hadj T₂]
    rfl
  · have hadj' : raiseIndex V B₂.flip = LinearMap.adjoint (raiseIndex V B₂) := by
      refine LinearMap.ext fun u => ext_inner_right ℝ fun w => ?_
      rw [inner_raiseIndex, LinearMap.flip_apply, LinearMap.adjoint_inner_left,
        real_inner_comm, inner_raiseIndex]
    rw [tensorContraction_lowerIndex, hadj']
    rfl

end TensorExercises

/-! ## A vanishing lemma for interval integrals

Shared by the equality cases of Exercises 1.6.18 and 1.6.19. -/

/-- **Eng.** A continuous function that is nonnegative on `[a, b]` (`a < b`)
and has vanishing integral over `[a, b]` vanishes identically on `[a, b]`. -/
theorem eqOn_zero_of_intervalIntegral_eq_zero {f : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (hab : a < b) (hnn : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hzero : ∫ t in a..b, f t = 0) :
    ∀ t ∈ Icc a b, f t = 0 := by
  intro t₀ ht₀
  by_contra hne
  have hpos : 0 < f t₀ := (hnn t₀ ht₀).lt_of_ne (Ne.symm hne)
  -- a neighbourhood of `t₀` on which `f > f t₀ / 2`
  have hmem : {s | f t₀ / 2 < f s} ∈ 𝓝 t₀ :=
    hf.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (half_lt_self hpos))
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hmem
  set α := max a (t₀ - δ / 2) with hα
  set β := min b (t₀ + δ / 2) with hβ
  have haα : a ≤ α := le_max_left _ _
  have hβb : β ≤ b := min_le_left _ _
  have hαβ : α < β := by
    apply max_lt <;> apply lt_min
    · exact hab
    · linarith [ht₀.1]
    · linarith [ht₀.2]
    · linarith
  have hαb : α ≤ b := by
    apply max_le hab.le
    linarith [ht₀.2]
  have haβ : a ≤ β := haα.trans hαβ.le
  have hIccαβ : Icc α β ⊆ Metric.ball t₀ δ := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    constructor
    · have := hs.2.trans (min_le_right b (t₀ + δ / 2))
      linarith
    · have := (le_max_right a (t₀ - δ / 2)).trans hs.1
      linarith
  have hint : IntervalIntegrable f MeasureTheory.volume a b := hf.intervalIntegrable a b
  have hsplit : (∫ t in a..α, f t) + (∫ t in α..β, f t) + (∫ t in β..b, f t)
      = ∫ t in a..b, f t := by
    rw [intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable a α) (hf.intervalIntegrable α β),
      intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable a β) (hf.intervalIntegrable β b)]
  have h1 : 0 ≤ ∫ t in a..α, f t :=
    intervalIntegral.integral_nonneg haα fun s hs =>
      hnn s ⟨hs.1, hs.2.trans hαb⟩
  have h3 : 0 ≤ ∫ t in β..b, f t :=
    intervalIntegral.integral_nonneg hβb fun s hs =>
      hnn s ⟨haβ.trans hs.1, hs.2⟩
  have h2 : (β - α) * (f t₀ / 2) ≤ ∫ t in α..β, f t := by
    have hconst : ∫ t in α..β, f t₀ / 2 = (β - α) * (f t₀ / 2) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [← hconst]
    refine intervalIntegral.integral_mono_on hαβ.le
      (intervalIntegrable_const) (hf.intervalIntegrable α β) fun s hs => ?_
    exact (hδ (hIccαβ hs)).le
  have h2pos : 0 < (β - α) * (f t₀ / 2) :=
    mul_pos (by linarith) (by linarith)
  rw [hzero] at hsplit
  linarith

/-! ## Exercise 1.6.15 — the quotient map `𝔽ⁿ⁺¹ − {0} → 𝔽Pⁿ` -/

section Exercise15

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** Petersen §1.6, Exercise 1.6.15 (2), abstract core: a map
`F : V − {0} → N` from a punctured inner product space that is **invariant
under the scalar action** (`F(cx) = F(x)` for `c ≠ 0` — e.g. the projective
quotient map `x ↦ span{x}`) is **never a Riemannian submersion for the
standard flat metric**, no matter which metric `gN` the target carries.

Proof: by scale invariance and the chain rule, `DF_{cp}(cu) = DF_p(u)`, so
`ker DF_{cp} = ker DF_p` and a horizontal vector `u` at `p` is horizontal at
`cp` after scaling. If `DF` were isometric on horizontal vectors at both `p`
and `2p`, then `4|u|² = |2u|² = |DF_{2p}(2u)|² = |DF_p(u)|² = |u|²`, forcing
every horizontal vector into the kernel — contradicting surjectivity of
`DF_p` (the target is nontrivial).

The punctured domain is represented by restricting every hypothesis to
`x ≠ 0`; all conditions are local and `{x ≠ 0}` is open, so this is exactly
the Riemannian-submersion condition for the open submanifold `V − {0}`. -/
theorem not_riemannianSubmersion_of_smul_invariant
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V] [Nontrivial E']
    (gN : RiemannianMetric I' M') {F : V → M'}
    (hscale : ∀ (x : V) (c : ℝ), x ≠ 0 → c ≠ 0 → F (c • x) = F x)
    (hdiff : ∀ x : V, x ≠ 0 → MDifferentiableAt 𝓘(ℝ, V) I' F x)
    (hsurj : ∀ x : V, x ≠ 0 → Function.Surjective (mfderiv 𝓘(ℝ, V) I' F x))
    (hiso : ∀ x : V, x ≠ 0 → ∀ u v : V,
      (∀ w : V, mfderiv 𝓘(ℝ, V) I' F x w = 0 → ⟪u, w⟫_ℝ = 0) →
      (∀ w : V, mfderiv 𝓘(ℝ, V) I' F x w = 0 → ⟪v, w⟫_ℝ = 0) →
      ⟪u, v⟫_ℝ = gN.metricInner (F x) (mfderiv 𝓘(ℝ, V) I' F x u)
        (mfderiv 𝓘(ℝ, V) I' F x v)) :
    False := by
  obtain ⟨p, hp⟩ := exists_ne (0 : V)
  have h2p : (2 : ℝ) • p ≠ 0 := smul_ne_zero two_ne_zero hp
  have hFp : F ((2 : ℝ) • p) = F p := hscale p 2 hp two_ne_zero
  -- the chain rule: `DF_p(u) = DF_{2p}(2u)`
  have hkey : ∀ u : V,
      mfderiv 𝓘(ℝ, V) I' F p u
        = mfderiv 𝓘(ℝ, V) I' F ((2 : ℝ) • p) ((2 : ℝ) • u) := by
    have hcongr : F =ᶠ[𝓝 p] (F ∘ fun x : V => (2 : ℝ) • x) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hp] with x hx
      exact (hscale x 2 hx two_ne_zero).symm
    have hsmul_diff : DifferentiableAt ℝ (fun x : V => (2 : ℝ) • x) p :=
      (differentiable_id.const_smul (2 : ℝ)).differentiableAt
    have hs : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (fun x : V => (2 : ℝ) • x) p
        = (2 : ℝ) • ContinuousLinearMap.id ℝ V := by
      rw [mfderiv_eq_fderiv]
      exact ((hasFDerivAt_id p).const_smul (2 : ℝ)).fderiv
    have hd : mfderiv 𝓘(ℝ, V) I' F p
        = mfderiv 𝓘(ℝ, V) I' (F ∘ fun x : V => (2 : ℝ) • x) p :=
      hcongr.mfderiv_eq
    intro u
    rw [hd, mfderiv_comp p (hdiff _ h2p) hsmul_diff.mdifferentiableAt, hs]
    rfl
  -- kernels agree
  have hker : ∀ w : V, mfderiv 𝓘(ℝ, V) I' F ((2 : ℝ) • p) w = 0 →
      mfderiv 𝓘(ℝ, V) I' F p w = 0 := by
    intro w hw
    calc mfderiv 𝓘(ℝ, V) I' F p w
        = mfderiv 𝓘(ℝ, V) I' F ((2 : ℝ) • p) ((2 : ℝ) • w) := hkey w
      _ = (2 : ℝ) • mfderiv 𝓘(ℝ, V) I' F ((2 : ℝ) • p) w :=
          (mfderiv 𝓘(ℝ, V) I' F ((2 : ℝ) • p)).map_smul _ _
      _ = 0 := by rw [hw, smul_zero]
  -- a horizontal vector at `p` with nonzero image
  haveI : Nontrivial (TangentSpace I' (F p)) := inferInstanceAs (Nontrivial E')
  obtain ⟨w', hw'⟩ := exists_ne (0 : TangentSpace I' (F p))
  obtain ⟨u, hu⟩ : ∃ u : V, mfderiv 𝓘(ℝ, V) I' F p u = w' := hsurj p hp w'
  set D := mfderiv 𝓘(ℝ, V) I' F p with hD
  set K : Submodule ℝ V := LinearMap.ker D.toLinearMap with hK
  set h : V := u - K.starProjection u with hh
  have hhmem : h ∈ Kᗮ := K.sub_starProjection_mem_orthogonal u
  have hDh : D h = w' := by
    have hk : K.starProjection u ∈ K := K.starProjection_apply_mem u
    have hk0 : D (K.starProjection u) = 0 := LinearMap.mem_ker.mp hk
    have hsub : D h = D u - D (K.starProjection u) :=
      D.map_sub u (K.starProjection u)
    rw [hsub, hk0, sub_zero, hu]
  have hh0 : h ≠ 0 := by
    intro h0
    exact hw' (by rw [← hDh, h0]; exact map_zero D)
  have hperp : ∀ w : V, D w = 0 → ⟪h, w⟫_ℝ = 0 := by
    intro w hw
    have hwK : w ∈ K := LinearMap.mem_ker.mpr hw
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal K h).mp hhmem w hwK
  have hperp2 : ∀ w : V, mfderiv 𝓘(ℝ, V) I' F ((2 : ℝ) • p) w = 0 →
      ⟪(2 : ℝ) • h, w⟫_ℝ = 0 := by
    intro w hw
    rw [real_inner_smul_left, hperp w (hker w hw), mul_zero]
  have hA := hiso p hp h h hperp hperp
  have hB := hiso ((2 : ℝ) • p) h2p ((2 : ℝ) • h) ((2 : ℝ) • h) hperp2 hperp2
  rw [← hkey h] at hB
  rw [hFp] at hB
  have hcontr : ⟪(2 : ℝ) • h, (2 : ℝ) • h⟫_ℝ = ⟪h, h⟫_ℝ := by
    rw [hB, ← hA]
  rw [real_inner_smul_left, real_inner_smul_right] at hcontr
  have hinner0 : ⟪h, h⟫_ℝ = 0 := by nlinarith [hcontr]
  exact hh0 (inner_self_eq_zero.mp hinner0)

/-- **Math.** Petersen §1.6, Exercise 1.6.15 for `𝔽 = ℂ`, `n = 1`: the
quotient map `ℂ² − {0} → ℂP¹`, with `ℂP¹` realized (as in Example 1.1.5 /
Exercise 1.6.22) as the sphere `S²(1/2)` via the Hopf map:
`F(x) = Ĥ(x / ‖x‖)`, so that `F(x)` depends only on `span_ℂ{x}` and `F`
restricted to `S³` is the Hopf fibration `hopfMap`, a Riemannian submersion
(`hopfMap_isRiemannianSubmersion`). The junk value at `0` (an arbitrary
point of `S²(1/2)`) is irrelevant: all statements are restricted to
`x ≠ 0`. -/
def hopfQuotientMap (x : WithLp 2 (ℂ × ℂ)) : sphere (0 : WithLp 2 (ℝ × ℂ)) (1 / 2) :=
  if hx : x = 0 then
    have h : (sphere (0 : WithLp 2 (ℝ × ℂ)) (1 / 2)).Nonempty :=
      NormedSpace.sphere_nonempty.mpr (by norm_num)
    ⟨h.some, h.some_mem⟩
  else
    ⟨hopfMapAmbient (‖x‖⁻¹ • x), by
      haveI : NormSMulClass ℝ (WithLp 2 (ℂ × ℂ)) := NormedSpace.toNormSMulClass
      rw [mem_sphere_zero_iff_norm, norm_hopfMapAmbient, norm_smul, norm_inv,
        norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), one_pow]⟩

/-- **Eng.** The ambient Hopf map is quadratically homogeneous for the real
scalar action: `Ĥ(t • x) = t² • Ĥ(x)`. -/
theorem hopfMapAmbient_smul (t : ℝ) (x : WithLp 2 (ℂ × ℂ)) :
    hopfMapAmbient (t • x) = (t ^ 2 : ℝ) • hopfMapAmbient x := by
  apply WithLp.ofLp_injective 2
  refine Prod.ext ?_ ?_
  · show (‖t • x.snd‖ ^ 2 - ‖t • x.fst‖ ^ 2) / 2
      = t ^ 2 * ((‖x.snd‖ ^ 2 - ‖x.fst‖ ^ 2) / 2)
    rw [Complex.real_smul, Complex.real_smul, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]
    ring
  · show (t • x.fst) * starRingEnd ℂ (t • x.snd)
      = (t ^ 2 : ℝ) • (x.fst * starRingEnd ℂ x.snd)
    rw [Complex.real_smul, Complex.real_smul, Complex.real_smul, map_mul,
      Complex.conj_ofReal]
    push_cast
    ring

/-- **Math.** The Hopf quotient map is invariant under the (real) scalar
action: `F(cx) = F(x)` for `c ≠ 0` — its fibres contain the punctured real
lines through the origin (in fact the punctured complex lines, which is
Exercise 1.6.22 (4)). -/
theorem hopfQuotientMap_smul (x : WithLp 2 (ℂ × ℂ)) (c : ℝ)
    (hx : x ≠ 0) (hc : c ≠ 0) :
    hopfQuotientMap (c • x) = hopfQuotientMap x := by
  have hcx : c • x ≠ 0 := smul_ne_zero hc hx
  rw [hopfQuotientMap, hopfQuotientMap, dif_neg hcx, dif_neg hx]
  refine Subtype.ext ?_
  show hopfMapAmbient (‖c • x‖⁻¹ • c • x) = hopfMapAmbient (‖x‖⁻¹ • x)
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have habs : |c| ≠ 0 := abs_ne_zero.mpr hc
  have harg : ‖c • x‖⁻¹ • c • x = (‖c • x‖⁻¹ * c * ‖x‖) • ‖x‖⁻¹ • x := by
    match_scalars
    field_simp
  rw [harg, hopfMapAmbient_smul]
  have hscalar : (‖c • x‖⁻¹ * c * ‖x‖) ^ 2 = 1 := by
    haveI : NormSMulClass ℝ (WithLp 2 (ℂ × ℂ)) := NormedSpace.toNormSMulClass
    rw [norm_smul, Real.norm_eq_abs, mul_inv]
    field_simp
    rw [sq_abs]
  rw [hscalar]
  exact one_smul ℝ _

/-- **Eng.** Off the origin, the Hopf quotient map factors through the
radial projection: `F = H ∘ (x ↦ x/‖x‖)`. -/
theorem hopfQuotientMap_eq_hopfMap_unitSphereProj {x : WithLp 2 (ℂ × ℂ)}
    (hx : x ≠ 0) :
    hopfQuotientMap x = hopfMap (unitSphereProj x) := by
  refine Subtype.ext ?_
  rw [hopfQuotientMap, dif_neg hx]
  show hopfMapAmbient (‖x‖⁻¹ • x)
    = hopfMapAmbient (unitSphereProj x : WithLp 2 (ℂ × ℂ))
  rw [coe_unitSphereProj hx]
  rfl

/-- **Eng.** The factorization holds on a neighborhood of any `x ≠ 0`. -/
theorem hopfQuotientMap_eventuallyEq {x : WithLp 2 (ℂ × ℂ)} (hx : x ≠ 0) :
    hopfQuotientMap =ᶠ[𝓝 x] (hopfMap ∘ unitSphereProj) := by
  filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
  exact hopfQuotientMap_eq_hopfMap_unitSphereProj hy

/-- **Math.** Exercise 1.6.15 (1), differentiability: the quotient map
`ℂ² − {0} → ℂP¹ = S²(1/2)` is smooth away from the origin — it is the
composition of the radial projection onto `S³` with the Hopf fibration. -/
theorem mdifferentiableAt_hopfQuotientMap {x : WithLp 2 (ℂ × ℂ)} (hx : x ≠ 0) :
    MDifferentiableAt 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 2) hopfQuotientMap x := by
  refine MDifferentiableAt.congr_of_eventuallyEq ?_ (hopfQuotientMap_eventuallyEq hx)
  exact ((contMDiff_hopfMap (unitSphereProj x)).mdifferentiableAt (by simp)).comp x
    ((contMDiffAt_unitSphereProj hx).mdifferentiableAt (by simp))

/-- **Eng.** The chain rule for the Hopf quotient map:
`DF_x = DH_{x/‖x‖} ∘ D(radial projection)_x`. -/
theorem mfderiv_hopfQuotientMap {x : WithLp 2 (ℂ × ℂ)} (hx : x ≠ 0) :
    mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 2) hopfQuotientMap x
      = (mfderiv (𝓡 3) (𝓡 2) hopfMap (unitSphereProj x)).comp
          (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 3) unitSphereProj x) := by
  rw [(hopfQuotientMap_eventuallyEq hx).mfderiv_eq]
  exact mfderiv_comp x
    ((contMDiff_hopfMap (unitSphereProj x)).mdifferentiableAt (by simp))
    ((contMDiffAt_unitSphereProj hx).mdifferentiableAt (by simp))

/-- **Math.** Exercise 1.6.15 (1), submersion property: the differential of
the quotient map is surjective away from the origin — both factors are
submersions. -/
theorem mfderiv_hopfQuotientMap_surjective {x : WithLp 2 (ℂ × ℂ)} (hx : x ≠ 0) :
    Function.Surjective (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 2) hopfQuotientMap x) := by
  rw [mfderiv_hopfQuotientMap hx]
  intro t
  obtain ⟨s, hs⟩ := hopfMap_isRiemannianSubmersion.2.1 (unitSphereProj x) t
  obtain ⟨u, hu⟩ := mfderiv_unitSphereProj_surjective hx s
  refine ⟨u, ?_⟩
  show (mfderiv (𝓡 3) (𝓡 2) hopfMap (unitSphereProj x))
    ((mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 3) unitSphereProj x) u) = t
  rw [hu, hs]

/-- **Math.** The radial direction lies in the kernel of the quotient map's
differential: the map is constant along rays. -/
theorem mfderiv_hopfQuotientMap_self {x : WithLp 2 (ℂ × ℂ)} (hx : x ≠ 0) :
    mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 2) hopfQuotientMap x x = 0 := by
  rw [mfderiv_hopfQuotientMap hx]
  show (mfderiv (𝓡 3) (𝓡 2) hopfMap (unitSphereProj x))
    ((mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 3) unitSphereProj x) x) = 0
  rw [mfderiv_unitSphereProj_self hx, map_zero]

/-- **Eng.** The vertical vector at a point of `ℂ²`, paired against the
point itself: the `toLp`-form of `real_inner_toLp_hopfVertical`. -/
theorem real_inner_self_hopfVertical (x : WithLp 2 (ℂ × ℂ)) :
    ⟪x, hopfVertical x.fst x.snd⟫_ℝ = 0 :=
  real_inner_toLp_hopfVertical x.fst x.snd

/-- **Eng.** The vertical vector scales linearly under the radial
projection: `i·(x/‖x‖) = ‖x‖⁻¹ (i·x)`. -/
theorem hopfVertical_unitSphereProj {x : WithLp 2 (ℂ × ℂ)} (hx : x ≠ 0) :
    hopfVertical (unitSphereProj x : WithLp 2 (ℂ × ℂ)).fst
        (unitSphereProj x : WithLp 2 (ℂ × ℂ)).snd
      = ‖x‖⁻¹ • hopfVertical x.fst x.snd := by
  rw [coe_unitSphereProj hx]
  apply WithLp.ofLp_injective
  refine Prod.ext ?_ ?_
  · show Complex.I * (‖x‖⁻¹ • x.fst) = ‖x‖⁻¹ • (Complex.I * x.fst)
    rw [Complex.real_smul, Complex.real_smul]
    ring
  · show Complex.I * (‖x‖⁻¹ • x.snd) = ‖x‖⁻¹ • (Complex.I * x.snd)
    rw [Complex.real_smul, Complex.real_smul]
    ring

/-- **Math.** The Hopf-circle direction lies in the kernel of the quotient
map's differential: the vertical vector `i·x` is killed — its radial
projection is the vertical vector at `x/‖x‖`, which `DĤ` annihilates. -/
theorem mfderiv_hopfQuotientMap_vertical {x : WithLp 2 (ℂ × ℂ)} (hx : x ≠ 0) :
    mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 2) hopfQuotientMap x
      (hopfVertical x.fst x.snd) = 0 := by
  rw [mfderiv_hopfQuotientMap hx]
  show (mfderiv (𝓡 3) (𝓡 2) hopfMap (unitSphereProj x))
    ((mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 3) unitSphereProj x)
      (hopfVertical x.fst x.snd)) = 0
  apply mfderiv_coe_sphere_radius_injective (1 / 2) (hopfMap (unitSphereProj x))
  rw [map_zero, mfderiv_coe_hopfMap_apply, mfderiv_coe_unitSphereProj_apply hx,
    fderiv_inv_norm_smul_orthogonal hx (real_inner_self_hopfVertical x)]
  have hkey := congrArg (hopfDeriv (unitSphereProj x : WithLp 2 (ℂ × ℂ)).fst
    (unitSphereProj x : WithLp 2 (ℂ × ℂ)).snd) (hopfVertical_unitSphereProj hx)
  rw [hopfDeriv_hopfVertical] at hkey
  exact hkey.symm

/-- **Eng.** The real inner product as a plain continuous bilinear form:
the star-semilinear `innerSL ℝ` coerced along `starRingEnd ℝ = id`. Wrapped
as a definition so that the plain `→L[ℝ]` type is pinned once and for all
(inline ascriptions lose it under `•`). -/
noncomputable def innerFormReal (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ (E := E) : E →L[ℝ] E →L[ℝ] ℝ)

@[simp]
theorem innerFormReal_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) :
    innerFormReal E u v = ⟪u, v⟫_ℝ :=
  rfl

/-- **Math.** A vector `u` Euclidean-orthogonal to both the radial direction
`x` and the vertical direction `i·x` projects to a tangent vector of `S³`
that is `g`-orthogonal to the kernel of the Hopf differential: the ambient
image of a kernel vector decomposes into a vertical part and a horizontal
part, and the horizontal part is killed — `DĤ` is injective on horizontals
(`real_inner_hopfDeriv_hopfHorizontal`) — so it is a multiple of the
vertical vector at `x/‖x‖`, which pairs to zero with `u`. -/
theorem hopfMap_kernel_orthogonal {x : WithLp 2 (ℂ × ℂ)} (hx : x ≠ 0)
    {u : WithLp 2 (ℂ × ℂ)} (hux : ⟪x, u⟫_ℝ = 0)
    (huv : ⟪hopfVertical x.fst x.snd, u⟫_ℝ = 0)
    (t : TangentSpace (𝓡 3) (unitSphereProj x))
    (ht : mfderiv (𝓡 3) (𝓡 2) hopfMap (unitSphereProj x) t = 0) :
    (sphereMetricUnit (WithLp 2 (ℂ × ℂ))).metricInner (unitSphereProj x)
      (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 3) unitSphereProj x u) t = 0 := by
  set a : WithLp 2 (ℂ × ℂ) := mfderiv (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
    ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) (unitSphereProj x) t
    with ha
  -- `a` is tangent to the sphere at the projection point
  have hap : ⟪(unitSphereProj x : WithLp 2 (ℂ × ℂ)), a⟫_ℝ = 0 := by
    have hmem : (mfderiv (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
        ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) (unitSphereProj x)) t
        ∈ (mfderiv (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
        ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) (unitSphereProj x) :
        TangentSpace (𝓡 3) (unitSphereProj x) →L[ℝ] WithLp 2 (ℂ × ℂ)).range :=
      LinearMap.mem_range.mpr ⟨t, rfl⟩
    rw [range_mfderiv_coe_sphere (unitSphereProj x)] at hmem
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hmem
  -- `DĤ` kills `a`
  have hDa : hopfDeriv (unitSphereProj x : WithLp 2 (ℂ × ℂ)).fst
      (unitSphereProj x : WithLp 2 (ℂ × ℂ)).snd a = 0 := by
    have h := mfderiv_coe_hopfMap_apply (unitSphereProj x) t
    rw [ht, map_zero] at h
    rw [ha]
    exact h.symm
  -- the vertical vector at the projection point
  set pv : WithLp 2 (ℂ × ℂ) := hopfVertical (unitSphereProj x : WithLp 2 (ℂ × ℂ)).fst
    (unitSphereProj x : WithLp 2 (ℂ × ℂ)).snd with hpv
  have hpv_unit : ⟪pv, pv⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hpv, WithLp.prod_norm_sq_eq_of_L2,
      hopfVertical_fst, hopfVertical_snd, norm_mul, norm_mul, Complex.norm_I,
      one_mul, one_mul]
    exact norm_fst_sq_add_norm_snd_sq_coe_unitSphere (unitSphereProj x)
  have hppv : ⟪(unitSphereProj x : WithLp 2 (ℂ × ℂ)), pv⟫_ℝ = 0 := by
    rw [hpv]
    exact real_inner_self_hopfVertical _
  -- decompose `a` into its vertical and horizontal parts
  have hsm1 : ⟪(unitSphereProj x : WithLp 2 (ℂ × ℂ)), ⟪pv, a⟫_ℝ • pv⟫_ℝ
      = ⟪pv, a⟫_ℝ * ⟪(unitSphereProj x : WithLp 2 (ℂ × ℂ)), pv⟫_ℝ :=
    real_inner_smul_right _ _ _
  have hsm2 : ⟪pv, ⟪pv, a⟫_ℝ • pv⟫_ℝ = ⟪pv, a⟫_ℝ * ⟪pv, pv⟫_ℝ :=
    real_inner_smul_right _ _ _
  have hhp : ⟪WithLp.toLp 2 ((unitSphereProj x : WithLp 2 (ℂ × ℂ)).fst,
      (unitSphereProj x : WithLp 2 (ℂ × ℂ)).snd), a - ⟪pv, a⟫_ℝ • pv⟫_ℝ = 0 := by
    have htoLp : WithLp.toLp 2 ((unitSphereProj x : WithLp 2 (ℂ × ℂ)).fst,
        (unitSphereProj x : WithLp 2 (ℂ × ℂ)).snd)
        = (unitSphereProj x : WithLp 2 (ℂ × ℂ)) := rfl
    rw [htoLp, inner_sub_right, hsm1, hap, hppv, mul_zero, sub_zero]
  have hhv : ⟪pv, a - ⟪pv, a⟫_ℝ • pv⟫_ℝ = 0 := by
    rw [inner_sub_right, hsm2, hpv_unit, mul_one, sub_self]
  obtain ⟨l, hl⟩ := exists_hopfHorizontal_eq (unitSphereProj x : WithLp 2 (ℂ × ℂ)).fst
    (unitSphereProj x : WithLp 2 (ℂ × ℂ)).snd
    (norm_fst_sq_add_norm_snd_sq_coe_unitSphere (unitSphereProj x))
    (a - ⟪pv, a⟫_ℝ • pv) hhp hhv
  -- the horizontal part is killed injectively by `DĤ`
  have hDpv : hopfDeriv (unitSphereProj x : WithLp 2 (ℂ × ℂ)).fst
      (unitSphereProj x : WithLp 2 (ℂ × ℂ)).snd pv = 0 := by
    rw [hpv]
    exact hopfDeriv_hopfVertical _ _
  have hDsm : hopfDeriv (unitSphereProj x : WithLp 2 (ℂ × ℂ)).fst
      (unitSphereProj x : WithLp 2 (ℂ × ℂ)).snd (⟪pv, a⟫_ℝ • pv)
      = ⟪pv, a⟫_ℝ • hopfDeriv (unitSphereProj x : WithLp 2 (ℂ × ℂ)).fst
        (unitSphereProj x : WithLp 2 (ℂ × ℂ)).snd pv :=
    map_smul _ _ _
  have hDh : hopfDeriv (unitSphereProj x : WithLp 2 (ℂ × ℂ)).fst
      (unitSphereProj x : WithLp 2 (ℂ × ℂ)).snd (a - ⟪pv, a⟫_ℝ • pv) = 0 := by
    rw [map_sub, hDsm, hDpv, hDa]
    have hz : ⟪pv, a⟫_ℝ • (0 : WithLp 2 (ℝ × ℂ)) = 0 := smul_zero _
    rw [hz, sub_zero]
  have hl0 : l = 0 := by
    have h1 := real_inner_hopfDeriv_hopfHorizontal
      (unitSphereProj x : WithLp 2 (ℂ × ℂ)).fst
      (unitSphereProj x : WithLp 2 (ℂ × ℂ)).snd l l
    rw [← hl, hDh, inner_zero_left,
      norm_fst_sq_add_norm_snd_sq_coe_unitSphere (unitSphereProj x),
      one_pow, mul_one] at h1
    have hsq : Complex.normSq l = 0 := by
      have h2 := congrArg Complex.re (Complex.mul_conj l)
      rw [← h1] at h2
      simpa using h2.symm
    exact Complex.normSq_eq_zero.mp hsq
  have hh0 : a - ⟪pv, a⟫_ℝ • pv = 0 := by
    rw [hl, hl0]
    apply WithLp.ofLp_injective
    refine Prod.ext ?_ ?_ <;> simp [hopfHorizontal]
  have ha' : a = ⟪pv, a⟫_ℝ • pv := sub_eq_zero.mp hh0
  -- conclude: the pairing reduces to `⟪u, i·x⟫ = 0`
  have hcoe : mfderiv (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
      ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) (unitSphereProj x)
      (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 3) unitSphereProj x u) = ‖x‖⁻¹ • u :=
    (mfderiv_coe_unitSphereProj_apply hx u).trans
      (fderiv_inv_norm_smul_orthogonal hx hux)
  have hupv : ⟪u, pv⟫_ℝ = 0 := by
    have h4 : pv = ‖x‖⁻¹ • hopfVertical x.fst x.snd := by
      rw [hpv]
      exact hopfVertical_unitSphereProj hx
    have h5 : ⟪u, ‖x‖⁻¹ • hopfVertical x.fst x.snd⟫_ℝ
        = ‖x‖⁻¹ * ⟪u, hopfVertical x.fst x.snd⟫_ℝ := real_inner_smul_right _ _ _
    have h6 : ⟪u, hopfVertical x.fst x.snd⟫_ℝ = 0 := by
      rw [real_inner_comm]
      exact huv
    rw [h4, h5, h6, mul_zero]
  have hfin : ⟪‖x‖⁻¹ • u, ⟪pv, a⟫_ℝ • pv⟫_ℝ = 0 := by
    have e1 : ⟪‖x‖⁻¹ • u, ⟪pv, a⟫_ℝ • pv⟫_ℝ = ‖x‖⁻¹ * ⟪u, ⟪pv, a⟫_ℝ • pv⟫_ℝ :=
      real_inner_smul_left _ _ _
    have e2 : ⟪u, ⟪pv, a⟫_ℝ • pv⟫_ℝ = ⟪pv, a⟫_ℝ * ⟪u, pv⟫_ℝ :=
      real_inner_smul_right _ _ _
    rw [e1, e2, hupv, mul_zero, mul_zero]
  show ⟪mfderiv (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
      ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) (unitSphereProj x)
      (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 3) unitSphereProj x u), a⟫_ℝ = 0
  rw [hcoe, ha']
  exact hfin

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **Math.** **Exercise 1.6.15** (Petersen §1.6), for the map
`F : 𝔽ⁿ⁺¹ − {0} → 𝔽Pⁿ`, `F(x) = span_𝔽{x}`, with `𝔽Pⁿ` carrying the metric
that makes `F` restricted to the unit sphere a Riemannian submersion.
Instantiated (see the module docstring) at `𝔽 = ℂ`, `n = 1`, where the
library realizes `ℂP¹ = S²(1/2)` via the Hopf fibration
(`hopfQuotientMap = Ĥ(x/‖x‖)`, with `sphereMetric _ (1/2)` the Fubini–Study
metric — `hopfMap_isRiemannianSubmersion`); the punctured domain is
represented by restricting all conditions to `x ≠ 0`:

1. `F` is a submersion;
2. `F` is **not** a Riemannian submersion for the standard flat metric on
   `ℂ² − {0}` (this instantiates the abstract
   `not_riemannianSubmersion_of_smul_invariant`, which shows no target
   metric works — the answer to (2) for every `𝔽`, `n`, and realization);
3. some metric on `ℂ² − {0}` (namely the cylinder metric
   `dr² + g_{S³}`) does make `F` a Riemannian submersion — a smooth family
   of inner products on the punctured space, which on an open subset of a
   vector space is exactly a Riemannian metric. -/
theorem exercise1_6_15 :
    -- (1) `F` is a submersion on `ℂ² − {0}`
    ((∀ x : WithLp 2 (ℂ × ℂ), x ≠ 0 →
        MDifferentiableAt 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 2) hopfQuotientMap x) ∧
      (∀ x : WithLp 2 (ℂ × ℂ), x ≠ 0 →
        Function.Surjective
          (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 2) hopfQuotientMap x))) ∧
    -- (2) `F` is not a Riemannian submersion for the standard flat metric
    ¬ ((∀ x : WithLp 2 (ℂ × ℂ), x ≠ 0 →
          MDifferentiableAt 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 2) hopfQuotientMap x) ∧
        (∀ x : WithLp 2 (ℂ × ℂ), x ≠ 0 →
          Function.Surjective
            (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 2) hopfQuotientMap x)) ∧
        (∀ x : WithLp 2 (ℂ × ℂ), x ≠ 0 → ∀ u v : WithLp 2 (ℂ × ℂ),
          (∀ w : WithLp 2 (ℂ × ℂ),
            mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 2) hopfQuotientMap x w = 0 →
            ⟪u, w⟫_ℝ = 0) →
          (∀ w : WithLp 2 (ℂ × ℂ),
            mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 2) hopfQuotientMap x w = 0 →
            ⟪v, w⟫_ℝ = 0) →
          ⟪u, v⟫_ℝ = (sphereMetric (WithLp 2 (ℝ × ℂ)) (1 / 2)).metricInner
            (hopfQuotientMap x)
            (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 2) hopfQuotientMap x u)
            (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 2) hopfQuotientMap x v))) ∧
    -- (3) some (smooth, pointwise inner product) metric on `ℂ² − {0}` makes
    -- `F` a Riemannian submersion
    (∃ g : WithLp 2 (ℂ × ℂ) →
        (WithLp 2 (ℂ × ℂ) →L[ℝ] WithLp 2 (ℂ × ℂ) →L[ℝ] ℝ),
      ContDiffOn ℝ ∞ g {x | x ≠ 0} ∧
      (∀ x : WithLp 2 (ℂ × ℂ), x ≠ 0 →
        (∀ u v, g x u v = g x v u) ∧ (∀ u, u ≠ 0 → 0 < g x u u)) ∧
      (∀ x : WithLp 2 (ℂ × ℂ), x ≠ 0 → ∀ u v : WithLp 2 (ℂ × ℂ),
        (∀ w : WithLp 2 (ℂ × ℂ),
          mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 2) hopfQuotientMap x w = 0 →
          g x u w = 0) →
        (∀ w : WithLp 2 (ℂ × ℂ),
          mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 2) hopfQuotientMap x w = 0 →
          g x v w = 0) →
        g x u v = (sphereMetric (WithLp 2 (ℝ × ℂ)) (1 / 2)).metricInner
          (hopfQuotientMap x)
          (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 2) hopfQuotientMap x u)
          (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 2) hopfQuotientMap x v))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨fun x hx => mdifferentiableAt_hopfQuotientMap hx,
      fun x hx => mfderiv_hopfQuotientMap_surjective hx⟩
  · rintro ⟨hdiff, hsurj, hiso⟩
    exact not_riemannianSubmersion_of_smul_invariant
      (sphereMetric (WithLp 2 (ℝ × ℂ)) (1 / 2))
      (fun x c hx hc => hopfQuotientMap_smul x c hx hc) hdiff hsurj hiso
  · -- (3): the cylinder metric `g_x(u, v) = ⟪u_r, v_r⟫ + ‖x‖⁻² ⟪u_T, v_T⟫`
    -- (radial/tangential decomposition), in closed form
    -- `g_x = q⁻¹ ⟪·,·⟫ + (q⁻¹ − q⁻²) ⟪x,·⟫⟪x,·⟫` with `q = ‖x‖²`.
    set gC : WithLp 2 (ℂ × ℂ) →
        (WithLp 2 (ℂ × ℂ) →L[ℝ] WithLp 2 (ℂ × ℂ) →L[ℝ] ℝ) := fun x =>
      (‖x‖ ^ 2)⁻¹ • innerFormReal (WithLp 2 (ℂ × ℂ))
        + ((‖x‖ ^ 2)⁻¹ - ((‖x‖ ^ 2)⁻¹) ^ 2)
            • ((innerSL ℝ x).smulRight (innerSL ℝ x)) with hgC
    have hgC_apply : ∀ x u v : WithLp 2 (ℂ × ℂ), gC x u v
        = (‖x‖ ^ 2)⁻¹ * ⟪u, v⟫_ℝ
          + ((‖x‖ ^ 2)⁻¹ - ((‖x‖ ^ 2)⁻¹) ^ 2) * (⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ) := by
      intro x u v
      simp only [hgC, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
        Pi.smul_apply, ContinuousLinearMap.smulRight_apply, innerFormReal_apply,
        innerSL_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    refine ⟨gC, ?_, ?_, ?_⟩
    · -- smoothness on the punctured space
      intro x hx
      have hx' : (x : WithLp 2 (ℂ × ℂ)) ≠ 0 := hx
      haveI : NormSMulClass ℝ (WithLp 2 (ℂ × ℂ) →L[ℝ] WithLp 2 (ℂ × ℂ) →L[ℝ] ℝ) :=
        NormedSpace.toNormSMulClass (𝕜 := ℝ)
          (E := WithLp 2 (ℂ × ℂ) →L[ℝ] WithLp 2 (ℂ × ℂ) →L[ℝ] ℝ)
      apply ContDiffAt.contDiffWithinAt
      have hq : ContDiffAt ℝ ∞ (fun y : WithLp 2 (ℂ × ℂ) => (‖y‖ ^ 2)⁻¹) x :=
        (contDiff_norm_sq ℝ).contDiffAt.inv (by positivity)
      have hB : ContDiff ℝ ∞ (fun y : WithLp 2 (ℂ × ℂ) =>
          (innerSL ℝ y).smulRight (innerSL ℝ y)) :=
        (isBoundedBilinearMap_smulRight (𝕜 := ℝ)).contDiff.comp
          ((innerSL ℝ (E := WithLp 2 (ℂ × ℂ))).contDiff.prodMk
            (innerSL ℝ (E := WithLp 2 (ℂ × ℂ))).contDiff)
      exact (hq.smul contDiffAt_const).add ((hq.sub (hq.pow 2)).smul hB.contDiffAt)
    · -- symmetry and positivity
      intro x hx
      have hx' : (x : WithLp 2 (ℂ × ℂ)) ≠ 0 := hx
      have hqpos : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
      constructor
      · intro u v
        rw [hgC_apply, hgC_apply, real_inner_comm u v]
        ring
      · intro u hu
        rw [hgC_apply]
        have hcs := real_inner_mul_inner_self_le x u
        rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
        have hupos : (0 : ℝ) < ‖u‖ ^ 2 := by
          have hune : u ≠ 0 := hu
          positivity
        have hkey : (0 : ℝ) < ‖x‖ ^ 2 * ‖u‖ ^ 2
            + (‖x‖ ^ 2 - 1) * (⟪x, u⟫_ℝ * ⟪x, u⟫_ℝ) := by
          rcases eq_or_ne ⟪x, u⟫_ℝ 0 with h0 | h0
          · rw [h0]
            nlinarith
          · have hspos : 0 < ⟪x, u⟫_ℝ * ⟪x, u⟫_ℝ := mul_self_pos.mpr h0
            nlinarith
        have hexp : (‖x‖ ^ 2)⁻¹ * ⟪u, u⟫_ℝ
              + ((‖x‖ ^ 2)⁻¹ - ((‖x‖ ^ 2)⁻¹) ^ 2) * (⟪x, u⟫_ℝ * ⟪x, u⟫_ℝ)
            = ((‖x‖ ^ 2)⁻¹) ^ 2 * (‖x‖ ^ 2 * ‖u‖ ^ 2
              + (‖x‖ ^ 2 - 1) * (⟪x, u⟫_ℝ * ⟪x, u⟫_ℝ)) := by
          rw [real_inner_self_eq_norm_sq]
          field_simp
        rw [hexp]
        exact mul_pos (by positivity) hkey
    · -- the submersion-isometry condition on horizontal vectors
      intro x hx u v hu hv
      have hx' : (x : WithLp 2 (ℂ × ℂ)) ≠ 0 := hx
      have hqpos : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
      -- `u` is orthogonal to the radial direction …
      have hux : ⟪x, u⟫_ℝ = 0 := by
        have h := hu x (mfderiv_hopfQuotientMap_self hx')
        rw [hgC_apply] at h
        have hgoal : ⟪x, u⟫_ℝ = (‖x‖ ^ 2)⁻¹ * ⟪u, x⟫_ℝ
            + ((‖x‖ ^ 2)⁻¹ - ((‖x‖ ^ 2)⁻¹) ^ 2) * (⟪x, u⟫_ℝ * ⟪x, x⟫_ℝ) := by
          rw [real_inner_comm u x, real_inner_self_eq_norm_sq]
          field_simp
          ring
        rw [hgoal]
        exact h
      have hvx : ⟪x, v⟫_ℝ = 0 := by
        have h := hv x (mfderiv_hopfQuotientMap_self hx')
        rw [hgC_apply] at h
        have hgoal : ⟪x, v⟫_ℝ = (‖x‖ ^ 2)⁻¹ * ⟪v, x⟫_ℝ
            + ((‖x‖ ^ 2)⁻¹ - ((‖x‖ ^ 2)⁻¹) ^ 2) * (⟪x, v⟫_ℝ * ⟪x, x⟫_ℝ) := by
          rw [real_inner_comm v x, real_inner_self_eq_norm_sq]
          field_simp
          ring
        rw [hgoal]
        exact h
      -- … and to the vertical direction
      have huvert : ⟪hopfVertical x.fst x.snd, u⟫_ℝ = 0 := by
        have h := hu (hopfVertical x.fst x.snd) (mfderiv_hopfQuotientMap_vertical hx')
        rw [hgC_apply, hux] at h
        rw [real_inner_comm]
        have h' : (‖x‖ ^ 2)⁻¹ * ⟪u, hopfVertical x.fst x.snd⟫_ℝ = 0 := by
          rw [← h]
          ring
        exact (mul_eq_zero.mp h').resolve_left (inv_ne_zero hqpos.ne')
      have hvvert : ⟪hopfVertical x.fst x.snd, v⟫_ℝ = 0 := by
        have h := hv (hopfVertical x.fst x.snd) (mfderiv_hopfQuotientMap_vertical hx')
        rw [hgC_apply, hvx] at h
        rw [real_inner_comm]
        have h' : (‖x‖ ^ 2)⁻¹ * ⟪v, hopfVertical x.fst x.snd⟫_ℝ = 0 := by
          rw [← h]
          ring
        exact (mul_eq_zero.mp h').resolve_left (inv_ne_zero hqpos.ne')
      -- apply the Hopf submersion's isometry clause to the projected vectors
      have hiso := hopfMap_isRiemannianSubmersion.2.2 (unitSphereProj x)
        (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 3) unitSphereProj x u)
        (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 3) unitSphereProj x v)
        (fun t ht => hopfMap_kernel_orthogonal hx' hux huvert t ht)
        (fun t ht => hopfMap_kernel_orthogonal hx' hvx hvvert t ht)
      -- the round metric of the projections computes the cylinder metric
      have hround : (sphereMetricUnit (WithLp 2 (ℂ × ℂ))).metricInner (unitSphereProj x)
          (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 3) unitSphereProj x u)
          (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 3) unitSphereProj x v)
          = gC x u v := by
        rw [sphereMetricUnit_apply, mfderiv_coe_unitSphereProj_apply hx',
          mfderiv_coe_unitSphereProj_apply hx',
          fderiv_inv_norm_smul_orthogonal hx' hux,
          fderiv_inv_norm_smul_orthogonal hx' hvx]
        have e1 : ⟪‖x‖⁻¹ • u, ‖x‖⁻¹ • v⟫_ℝ = ‖x‖⁻¹ * (‖x‖⁻¹ * ⟪u, v⟫_ℝ) := by
          have e1a : ⟪‖x‖⁻¹ • u, ‖x‖⁻¹ • v⟫_ℝ = ‖x‖⁻¹ * ⟪u, ‖x‖⁻¹ • v⟫_ℝ :=
            real_inner_smul_left _ _ _
          have e1b : ⟪u, ‖x‖⁻¹ • v⟫_ℝ = ‖x‖⁻¹ * ⟪u, v⟫_ℝ :=
            real_inner_smul_right _ _ _
          rw [e1a, e1b]
        refine e1.trans ?_
        rw [hgC_apply, hux]
        have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx'
        field_simp
        ring
      -- express the target inner product through the ambient Hopf differential
      rw [sphereMetric_apply] at hiso
      rw [mfderiv_coe_hopfMap_apply, mfderiv_coe_hopfMap_apply] at hiso
      rw [mfderiv_coe_unitSphereProj_apply hx', mfderiv_coe_unitSphereProj_apply hx',
        fderiv_inv_norm_smul_orthogonal hx' hux,
        fderiv_inv_norm_smul_orthogonal hx' hvx] at hiso
      -- the ambient differential of the quotient map on tangential vectors
      have hcoeF : ∀ w : WithLp 2 (ℂ × ℂ), ⟪x, w⟫_ℝ = 0 →
          mfderiv (𝓡 2) 𝓘(ℝ, WithLp 2 (ℝ × ℂ))
            ((↑) : sphere (0 : WithLp 2 (ℝ × ℂ)) (1 / 2) → WithLp 2 (ℝ × ℂ))
            (hopfQuotientMap x)
            (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (𝓡 2) hopfQuotientMap x w)
          = hopfDeriv (unitSphereProj x : WithLp 2 (ℂ × ℂ)).fst
              (unitSphereProj x : WithLp 2 (ℂ × ℂ)).snd (‖x‖⁻¹ • w) := by
        intro w hw
        have hFd := mdifferentiableAt_hopfQuotientMap hx'
        have hι' : MDifferentiableAt (𝓡 2) 𝓘(ℝ, WithLp 2 (ℝ × ℂ))
            ((↑) : sphere (0 : WithLp 2 (ℝ × ℂ)) (1 / 2) → WithLp 2 (ℝ × ℂ))
            (hopfQuotientMap x) :=
          (contMDiff_coe_sphere_radius (m := 1) (1 / 2)
            (hopfQuotientMap x)).mdifferentiableAt one_ne_zero
        have h1 := mfderiv_comp x hι' hFd
        have hev : (((↑) : sphere (0 : WithLp 2 (ℝ × ℂ)) (1 / 2) → WithLp 2 (ℝ × ℂ))
            ∘ hopfQuotientMap) =ᶠ[𝓝 x]
            (hopfMapAmbient ∘ fun y : WithLp 2 (ℂ × ℂ) => ‖y‖⁻¹ • y) := by
          filter_upwards [isOpen_compl_singleton.mem_nhds hx'] with y hy
          have hy' : y ≠ 0 := hy
          show (hopfQuotientMap y : WithLp 2 (ℝ × ℂ)) = hopfMapAmbient (‖y‖⁻¹ • y)
          rw [hopfQuotientMap, dif_neg hy']
        have hradd : DifferentiableAt ℝ (fun y : WithLp 2 (ℂ × ℂ) => ‖y‖⁻¹ • y) x :=
          (contDiffAt_inv_norm_smul hx').differentiableAt (by simp)
        have hcomp : HasFDerivAt
            (hopfMapAmbient ∘ fun y : WithLp 2 (ℂ × ℂ) => ‖y‖⁻¹ • y)
            ((hopfDeriv (‖x‖⁻¹ • x : WithLp 2 (ℂ × ℂ)).fst
              (‖x‖⁻¹ • x : WithLp 2 (ℂ × ℂ)).snd).comp
              (fderiv ℝ (fun y : WithLp 2 (ℂ × ℂ) => ‖y‖⁻¹ • y) x)) x :=
          HasFDerivAt.comp (g := hopfMapAmbient)
            (f := fun y : WithLp 2 (ℂ × ℂ) => ‖y‖⁻¹ • y) x
            (hasFDerivAt_hopfMapAmbient (‖x‖⁻¹ • x)) hradd.hasFDerivAt
        have h2 : mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) 𝓘(ℝ, WithLp 2 (ℝ × ℂ))
            (((↑) : sphere (0 : WithLp 2 (ℝ × ℂ)) (1 / 2) → WithLp 2 (ℝ × ℂ))
              ∘ hopfQuotientMap) x
            = (hopfDeriv (‖x‖⁻¹ • x : WithLp 2 (ℂ × ℂ)).fst
                (‖x‖⁻¹ • x : WithLp 2 (ℂ × ℂ)).snd).comp
                (fderiv ℝ (fun y : WithLp 2 (ℂ × ℂ) => ‖y‖⁻¹ • y) x) := by
          rw [hev.mfderiv_eq, mfderiv_eq_fderiv]
          exact hcomp.fderiv
        have hbase : (‖x‖⁻¹ • x : WithLp 2 (ℂ × ℂ))
            = (unitSphereProj x : WithLp 2 (ℂ × ℂ)) := (coe_unitSphereProj hx').symm
        rw [hbase] at h2
        have h3 := h1.symm.trans h2
        have h4 : fderiv ℝ (fun y : WithLp 2 (ℂ × ℂ) => ‖y‖⁻¹ • y) x w = ‖x‖⁻¹ • w :=
          fderiv_inv_norm_smul_orthogonal hx' hw
        have h5 : ((hopfDeriv (unitSphereProj x : WithLp 2 (ℂ × ℂ)).fst
            (unitSphereProj x : WithLp 2 (ℂ × ℂ)).snd).comp
            (fderiv ℝ (fun y : WithLp 2 (ℂ × ℂ) => ‖y‖⁻¹ • y) x)) w
            = hopfDeriv (unitSphereProj x : WithLp 2 (ℂ × ℂ)).fst
              (unitSphereProj x : WithLp 2 (ℂ × ℂ)).snd (‖x‖⁻¹ • w) := by
          show hopfDeriv (unitSphereProj x : WithLp 2 (ℂ × ℂ)).fst
              (unitSphereProj x : WithLp 2 (ℂ × ℂ)).snd
              (fderiv ℝ (fun y : WithLp 2 (ℂ × ℂ) => ‖y‖⁻¹ • y) x w)
            = hopfDeriv (unitSphereProj x : WithLp 2 (ℂ × ℂ)).fst
              (unitSphereProj x : WithLp 2 (ℂ × ℂ)).snd (‖x‖⁻¹ • w)
          rw [h4]
        exact (DFunLike.congr_fun h3 w).trans h5
      -- assemble
      rw [sphereMetric_apply, hcoeF u hux, hcoeF v hvx]
      exact hround.symm.trans hiso

end Exercise15

/-! ## Exercises 1.6.16–1.6.18 — arc length under maps -/

section ArcLengthExercises

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** **Exercise 1.6.16** (Petersen §1.6), parts (1) and (2), for the
arc length `L(c)|_a^b = ∫_a^b |ċ| dt` (`arcLength`):

1. **arc length does not depend on the parametrization**: for a smooth
   monotone reparametrization `φ`, `L(c ∘ φ)|_a^b = L(c)|_{φ(a)}^{φ(b)}`
   (this is `arcLength_reparam`);
2. **any curve of nowhere-vanishing speed can be reparametrized to unit
   speed**: there is a `φ` inverting the arc-length function
   `σ : t ↦ L(c)|_a^t` — differentiable at every point of the range of `σ` —
   such that `c ∘ φ` has speed `1` there. (`φ` is produced by the inverse
   function theorem: `σ' = |ċ| > 0`.)

Part (3) of the exercise — extending arc length to absolutely continuous
curves, and well-definedness of absolute continuity on manifolds — is not
formalized: Mathlib has no theory of absolutely continuous functions to state
it against. -/
-- TODO(PET.1): formalize part (3) once Mathlib gains absolutely continuous
-- functions (AC ↔ indefinite Bochner integral of an `L¹` derivative).
theorem exercise1_6_16 (g : RiemannianMetric I M) {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c) (a b : ℝ) :
    (∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → MonotoneOn φ (Set.uIcc a b) →
      arcLength g (c ∘ φ) a b = arcLength g c (φ a) (φ b)) ∧
    ((∀ t, 0 < g.metricInner (c t) (velocity c t) (velocity c t)) →
      ∃ φ : ℝ → ℝ,
        (∀ t, φ (arcLength g c a t) = t) ∧
        (∀ t, DifferentiableAt ℝ φ (arcLength g c a t)) ∧
        (∀ t, g.metricInner ((c ∘ φ) (arcLength g c a t))
          (velocity (c ∘ φ) (arcLength g c a t))
          (velocity (c ∘ φ) (arcLength g c a t)) = 1)) := by
  constructor
  · intro φ hφ hmono
    exact arcLength_reparam g hc hφ a b hmono
  · intro hspeed
    set s : ℝ → ℝ :=
      fun t => Real.sqrt (g.metricInner (c t) (velocity c t) (velocity c t))
      with hs_def
    have hs_cont : Continuous s := continuous_sqrt_metricInner_velocity g hc
    have hs_pos : ∀ t, 0 < s t := fun t => Real.sqrt_pos.mpr (hspeed t)
    set σ : ℝ → ℝ := fun t => arcLength g c a t with hσ_def
    have hσ_eq : ∀ t, σ t = ∫ u in a..t, s u := fun t => rfl
    have hσd : ∀ t, HasStrictDerivAt σ (s t) t := by
      intro t
      exact intervalIntegral.integral_hasStrictDerivAt_right
        (hs_cont.intervalIntegrable a t)
        (hs_cont.stronglyMeasurableAtFilter _ _) hs_cont.continuousAt
    have hσ_mono : StrictMono σ := by
      apply strictMono_of_deriv_pos
      intro t
      rw [(hσd t).hasDerivAt.deriv]
      exact hs_pos t
    set φ := Function.invFun σ with hφ_def
    have hφσ : ∀ t, φ (σ t) = t :=
      fun t => Function.leftInverse_invFun hσ_mono.injective t
    have hφd : ∀ t, HasDerivAt φ (s t)⁻¹ (σ t) := by
      intro t
      exact ((hσd t).to_local_left_inverse (hs_pos t).ne'
        (Filter.Eventually.of_forall hφσ)).hasDerivAt
    refine ⟨φ, hφσ, fun t => (hφd t).differentiableAt, fun t => ?_⟩
    have hcdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I c (φ (σ t)) := by
      rw [hφσ t]
      exact (hc t).mdifferentiableAt (by simp)
    have hvel : velocity (I := I) (c ∘ φ) (σ t)
        = deriv φ (σ t) • velocity c (φ (σ t)) :=
      velocity_reparam (σ t) hcdiff (hφd t).differentiableAt
    have hderiv : deriv φ (σ t) = (s t)⁻¹ := (hφd t).deriv
    have hbase : (c ∘ φ) (σ t) = c t := by
      rw [Function.comp_apply, hφσ t]
    have hval : g.metricInner ((c ∘ φ) (σ t)) (velocity (c ∘ φ) (σ t))
        (velocity (c ∘ φ) (σ t))
        = (s t)⁻¹ * ((s t)⁻¹ *
          g.metricInner (c t) (velocity c t) (velocity c t)) := by
      rw [hvel, hderiv, hφσ t]
      show g.metricInner (c (φ (σ t))) ((s t)⁻¹ • velocity c t)
          ((s t)⁻¹ • velocity c t) = _
      rw [hφσ t, g.metricInner_smul_left, g.metricInner_smul_right]
    have hst : s t * s t = g.metricInner (c t) (velocity c t) (velocity c t) :=
      Real.mul_self_sqrt (hspeed t).le
    have hs0 : s t ≠ 0 := (hs_pos t).ne'
    rw [hval, ← hst]
    field_simp

/-- **Math.** **Exercise 1.6.17** (Petersen §1.6): **arc length is preserved
by Riemannian immersions**: if `F : (M, g_M) → (N, g_N)` is a Riemannian
(isometric) immersion, then `L(F ∘ c) = L(c)` for every curve `c` — because
`F` preserves the metric, the speed of `F ∘ c` equals the speed of `c`
pointwise (chain rule `velocity_comp`), so the integrals agree
(`PreservesMetric.arcLength`). In particular curves on `Sⁿ(R) ⊂ ℝⁿ⁺¹` or
`Hⁿ ⊂ ℝ^{n,1}` may be measured ambiently, as Exercises 1.6.20/21 do. -/
theorem exercise1_6_17 {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'}
    {F : M → M'} (hF : IsRiemannianImmersion gM gN F) {c : ℝ → M}
    (hc : MDifferentiable 𝓘(ℝ, ℝ) I c) (a b : ℝ) :
    arcLength gN (F ∘ c) a b = arcLength gM c a b :=
  hF.2.arcLength (hF.1.1.mdifferentiable (by simp)) hc a b

section Submersion

variable [FiniteDimensional ℝ E]

/-- **Math.** Pointwise core of Exercise 1.6.18: under a Riemannian submersion,
`|DF(v)|² ≤ |v|²`, with equality iff `v ⊥ ker DF`. Decompose `v = k + h`
against `K = ker DF_p` with respect to `g_M`-orthogonality
(`LinearMap.BilinForm.orthogonal`; the restriction of the positive-definite
`g_M` to `K` is nondegenerate, so `T_pM = K ⊕ K^⊥`); then
`|DF v|² = |DF h|² = |h|²` and `|v|² = |k|² + |h|²`. -/
theorem IsRiemannianSubmersion.metricInner_mfderiv_le_and_eq_iff
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {F : M → M'}
    (hF : IsRiemannianSubmersion gM gN F) (p : M) (v : TangentSpace I p) :
    gN.metricInner (F p) (mfderiv I I' F p v) (mfderiv I I' F p v)
      ≤ gM.metricInner p v v ∧
    (gN.metricInner (F p) (mfderiv I I' F p v) (mfderiv I I' F p v)
        = gM.metricInner p v v ↔
      ∀ w : TangentSpace I p, mfderiv I I' F p w = 0 →
        gM.metricInner p v w = 0) := by
  classical
  set D := mfderiv I I' F p with hD
  set B : LinearMap.BilinForm ℝ (TangentSpace I p) :=
    LinearMap.mk₂ ℝ (fun u w => gM.metricInner p u w)
      (fun u u' w => gM.metricInner_add_left p u u' w)
      (fun r u w => gM.metricInner_smul_left p r u w)
      (fun u w w' => gM.metricInner_add_right p u w w')
      (fun r u w => gM.metricInner_smul_right p r u w)
    with hB
  have hB_apply : ∀ u w : TangentSpace I p, B u w = gM.metricInner p u w :=
    fun u w => rfl
  have hB_symm : ∀ u w : TangentSpace I p, B u w = B w u := by
    intro u w
    rw [hB_apply, hB_apply]
    exact gM.metricInner_comm p u w
  have hB_refl : B.IsRefl := by
    intro u w huw
    rw [← hB_symm]
    exact huw
  have hB_defin : ∀ u : TangentSpace I p, B u u = 0 → u = 0 := by
    intro u hu
    by_contra hne
    exact absurd (hB_apply u u ▸ hu) (gM.metricInner_self_pos p u hne).ne'
  set K : Submodule ℝ (TangentSpace I p) := LinearMap.ker D.toLinearMap with hK
  have hnd : (B.restrict K).Nondegenerate := by
    have hsepl : (B.restrict K).SeparatingLeft := by
      rintro ⟨u, huK⟩ hres
      refine Subtype.ext (hB_defin u ?_)
      simpa using hres ⟨u, huK⟩
    refine ⟨hsepl, fun y hy => hsepl y fun x => ?_⟩
    have hsymm : B.restrict K y x = B.restrict K x y := hB_symm _ _
    rw [hsymm]
    exact hy x
  have hcompl : IsCompl K (B.orthogonal K) :=
    B.isCompl_orthogonal_of_restrict_nondegenerate hB_refl hnd
  obtain ⟨k, hk, h, hh, hkh⟩ :
      ∃ k ∈ K, ∃ h ∈ B.orthogonal K, k + h = v := by
    have hv : v ∈ K ⊔ B.orthogonal K := by
      rw [hcompl.sup_eq_top]
      trivial
    obtain ⟨k, hk, h, hh, hkh⟩ := Submodule.mem_sup.mp hv
    exact ⟨k, hk, h, hh, hkh⟩
  have hDk : D k = 0 := LinearMap.mem_ker.mp hk
  have hDv : D v = D h := by rw [← hkh, map_add, hDk, zero_add]
  -- `h` is horizontal
  have hperp : ∀ w : TangentSpace I p, D w = 0 → gM.metricInner p h w = 0 := by
    intro w hw
    have hwK : w ∈ K := LinearMap.mem_ker.mpr hw
    rw [← hB_apply, hB_symm]
    exact hh w hwK
  have hiso : gM.metricInner p h h
      = gN.metricInner (F p) (D h) (D h) := hF.2.2 p h h hperp hperp
  have hkh_inner : gM.metricInner p v v
      = gM.metricInner p k k + gM.metricInner p h h := by
    rw [← hkh, gM.metricInner_add_left, gM.metricInner_add_right,
      gM.metricInner_add_right]
    have h1 : gM.metricInner p k h = 0 := by
      rw [gM.metricInner_comm]
      exact hperp k hDk
    have h2 : gM.metricInner p h k = 0 := hperp k hDk
    linarith
  have hknn : 0 ≤ gM.metricInner p k k := gM.metricInner_self_nonneg p k
  constructor
  · rw [hDv, ← hiso, hkh_inner]
    linarith
  · constructor
    · -- equality → perpendicular
      intro heq w hw
      have hk0 : gM.metricInner p k k = 0 := by
        rw [hDv, ← hiso] at heq
        linarith [hkh_inner]
      have hkz : k = 0 := hB_defin k (hB_apply k k ▸ hk0)
      have hvh : v = h := by rw [← hkh, hkz, zero_add]
      rw [hvh]
      exact hperp w hw
    · -- perpendicular → equality
      intro hvperp
      have hk0 : gM.metricInner p k k = 0 := by
        have h1 : gM.metricInner p v k = 0 := hvperp k hDk
        have h2 : gM.metricInner p h k = 0 := hperp k hDk
        have h3 : gM.metricInner p v k
            = gM.metricInner p k k + gM.metricInner p h k := by
          rw [← hkh, gM.metricInner_add_left]
        linarith
      rw [hkh_inner, hk0, zero_add, hDv, ← hiso]

/-- **Math.** **Exercise 1.6.18** (Petersen §1.6): for a Riemannian submersion
`F : (M, g_M) → (N, g_N)` and a curve `c : [a, b] → M`,
**`L(F ∘ c) ≤ L(c)`**, with **equality iff `ċ(t) ⊥ ker DF_{c(t)}` for all
`t ∈ [a, b]`**. Pointwise, `|D F(ċ)| ≤ |ċ|` with equality iff `ċ` is
horizontal (`metricInner_mfderiv_le_and_eq_iff`); integrating gives the
inequality, and for `a < b` the equality case follows because the continuous
nonnegative defect `|ċ| − |(F∘c)˙|` has vanishing integral iff it vanishes
identically. (For `a = b` both lengths are `0` and the integral identity
carries no pointwise information, so the reverse implication is stated for
`a < b`.) -/
theorem exercise1_6_18 {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'}
    {F : M → M'} (hF : IsRiemannianSubmersion gM gN F) {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c) {a b : ℝ} (hab : a ≤ b) :
    arcLength gN (F ∘ c) a b ≤ arcLength gM c a b ∧
    ((∀ t ∈ Icc a b, ∀ w : TangentSpace I (c t),
        mfderiv I I' F (c t) w = 0 → gM.metricInner (c t) (velocity c t) w = 0) →
      arcLength gN (F ∘ c) a b = arcLength gM c a b) ∧
    (a < b → arcLength gN (F ∘ c) a b = arcLength gM c a b →
      ∀ t ∈ Icc a b, ∀ w : TangentSpace I (c t),
        mfderiv I I' F (c t) w = 0 → gM.metricInner (c t) (velocity c t) w = 0) := by
  have hFc : ContMDiff 𝓘(ℝ, ℝ) I' ∞ (F ∘ c) := hF.1.comp hc
  have hvel : ∀ t, velocity (F ∘ c) t = mfderiv I I' F (c t) (velocity c t) :=
    fun t => velocity_comp t ((hF.1 (c t)).mdifferentiableAt (by simp))
      ((hc t).mdifferentiableAt (by simp))
  set sM : ℝ → ℝ :=
    fun t => Real.sqrt (gM.metricInner (c t) (velocity c t) (velocity c t))
    with hsM
  set sN : ℝ → ℝ :=
    fun t => Real.sqrt (gN.metricInner ((F ∘ c) t) (velocity (F ∘ c) t)
      (velocity (F ∘ c) t)) with hsN
  have hsM_cont : Continuous sM := continuous_sqrt_metricInner_velocity gM hc
  have hsN_cont : Continuous sN := continuous_sqrt_metricInner_velocity gN hFc
  have hinner_eq : ∀ t, gN.metricInner ((F ∘ c) t) (velocity (F ∘ c) t)
      (velocity (F ∘ c) t)
      = gN.metricInner (F (c t)) (mfderiv I I' F (c t) (velocity c t))
        (mfderiv I I' F (c t) (velocity c t)) := by
    intro t
    rw [hvel t]
    rfl
  have hptle : ∀ t, sN t ≤ sM t := by
    intro t
    rw [hsN, hsM]
    apply Real.sqrt_le_sqrt
    rw [hinner_eq t]
    exact (hF.metricInner_mfderiv_le_and_eq_iff (c t) (velocity c t)).1
  have hLM : arcLength gM c a b = ∫ t in a..b, sM t := rfl
  have hLN : arcLength gN (F ∘ c) a b = ∫ t in a..b, sN t := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hLM, hLN]
    exact intervalIntegral.integral_mono_on hab (hsN_cont.intervalIntegrable a b)
      (hsM_cont.intervalIntegrable a b) fun t _ => hptle t
  · intro hperp
    rw [hLM, hLN]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hab] at ht
    have heq := (hF.metricInner_mfderiv_le_and_eq_iff (c t) (velocity c t)).2.mpr
      (hperp t ht)
    simp only [hsN, hsM]
    rw [hinner_eq t, heq]
  · intro hab' heq t ht w hw
    -- the defect `sM - sN` is continuous, nonnegative, and has zero integral
    have hzero : ∫ u in a..b, (sM u - sN u) = 0 := by
      rw [intervalIntegral.integral_sub (hsM_cont.intervalIntegrable a b)
        (hsN_cont.intervalIntegrable a b), ← hLM, ← hLN, heq, sub_self]
    have hvanish := eqOn_zero_of_intervalIntegral_eq_zero
      (hsM_cont.sub hsN_cont) hab' (fun u _ => sub_nonneg.mpr (hptle u)) hzero
    have hsMN : sN t = sM t := by
      have := hvanish t ht
      linarith
    have hinner : gN.metricInner (F (c t))
        (mfderiv I I' F (c t) (velocity c t))
        (mfderiv I I' F (c t) (velocity c t))
        = gM.metricInner (c t) (velocity c t) (velocity c t) := by
      have h1 : Real.sqrt (gN.metricInner (F (c t))
          (mfderiv I I' F (c t) (velocity c t))
          (mfderiv I I' F (c t) (velocity c t)))
          = Real.sqrt (gM.metricInner (c t) (velocity c t) (velocity c t)) := by
        rw [← hinner_eq t]
        exact hsMN
      calc gN.metricInner (F (c t)) (mfderiv I I' F (c t) (velocity c t))
            (mfderiv I I' F (c t) (velocity c t))
          = Real.sqrt (gN.metricInner (F (c t))
              (mfderiv I I' F (c t) (velocity c t))
              (mfderiv I I' F (c t) (velocity c t))) ^ 2 :=
            (Real.sq_sqrt (gN.metricInner_self_nonneg (F (c t))
              (mfderiv I I' F (c t) (velocity c t)))).symm
        _ = Real.sqrt (gM.metricInner (c t) (velocity c t) (velocity c t)) ^ 2 :=
            by rw [h1]
        _ = gM.metricInner (c t) (velocity c t) (velocity c t) :=
            Real.sq_sqrt (gM.metricInner_self_nonneg (c t) (velocity c t))
    exact (hF.metricInner_mfderiv_le_and_eq_iff (c t) (velocity c t)).2.mp
      hinner w hw

end Submersion

end ArcLengthExercises

/-! ## Exercise 1.6.19 — straight lines minimize in Euclidean space -/

section Exercise19

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [CompleteSpace W]

/-- **Math.** **Exercise 1.6.19** (Petersen §1.6): **any curve between two
points of Euclidean space is at least as long as the distance between them,
and if the length equals the distance the curve lies on the connecting
segment.** Formalized on a real inner product space (Petersen's `ℝⁿ`):

1. `|c(b) − c(a)| = |∫ ċ| ≤ ∫ |ċ| = L(c)`;
2. in the equality case, with `v = (c(b) − c(a))/|c(b) − c(a)|` (the hint's
   unit vector), the continuous defect `|ċ| − ⟪v, ċ⟫ ≥ 0` integrates to zero,
   hence vanishes; the Cauchy–Schwarz equality case gives `ċ = |ċ| v`, so by
   the fundamental theorem of calculus `c(t) = c(a) + (∫_a^t |ċ|) v` traces
   the segment monotonically. -/
theorem exercise1_6_19 {c : ℝ → W} (hc : ContDiff ℝ ∞ c) {a b : ℝ}
    (hab : a ≤ b) :
    dist (c a) (c b) ≤ arcLength (innerProductSpaceMetric W) c a b ∧
    (arcLength (innerProductSpaceMetric W) c a b = dist (c a) (c b) →
      ∀ t ∈ Icc a b, c t ∈ segment ℝ (c a) (c b)) := by
  have hcd : Differentiable ℝ c := hc.differentiable (by simp)
  have hderiv_cont : Continuous (deriv c) := hc.continuous_deriv (by simp)
  have hFTC : ∀ u, ∫ s in a..u, deriv c s = c u - c a := by
    intro u
    exact intervalIntegral.integral_deriv_eq_sub (fun s _ => hcd s)
      (hderiv_cont.intervalIntegrable a u)
  have hL : arcLength (innerProductSpaceMetric W) c a b
      = ∫ t in a..b, ‖deriv c t‖ := arcLength_eq_integral_norm_deriv c a b
  have hdist : dist (c a) (c b) = ‖c b - c a‖ := by
    rw [dist_eq_norm, norm_sub_rev]
  have hineq : dist (c a) (c b) ≤ arcLength (innerProductSpaceMetric W) c a b := by
    rw [hL, hdist, ← hFTC b]
    exact intervalIntegral.norm_integral_le_integral_norm hab
  refine ⟨hineq, fun heq t ht => ?_⟩
  rcases eq_or_lt_of_le hab with rfl | hab'
  · obtain rfl : t = a := le_antisymm ht.2 ht.1
    exact left_mem_segment ℝ _ _
  by_cases hpq : c b = c a
  · -- endpoints agree: zero length forces a constant curve
    have hL0 : ∫ u in a..b, ‖deriv c u‖ = 0 := by
      rw [← hL, heq, hdist, hpq, sub_self, norm_zero]
    have hnorm0 : ∀ u ∈ Icc a b, ‖deriv c u‖ = 0 :=
      eqOn_zero_of_intervalIntegral_eq_zero hderiv_cont.norm hab'
        (fun u _ => norm_nonneg _) hL0
    have hconst : ∀ u ∈ Icc a b, c u = c a := by
      intro u hu
      refine constant_of_has_deriv_right_zero hc.continuous.continuousOn
        (fun x hx => ?_) u hu
      have hzero : deriv c x = 0 :=
        norm_eq_zero.mp (hnorm0 x (Ico_subset_Icc_self hx))
      exact hzero ▸ (hcd x).hasDerivAt.hasDerivWithinAt
    rw [hconst t ht]
    exact left_mem_segment ℝ _ _
  -- main case: distinct endpoints
  have hsub : c b - c a ≠ 0 := sub_ne_zero.mpr hpq
  set v : W := ‖c b - c a‖⁻¹ • (c b - c a) with hv
  have hvnorm : ‖v‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hsub
  set f : ℝ → ℝ := fun u => ‖deriv c u‖ - ⟪v, deriv c u⟫_ℝ with hf
  have hf_cont : Continuous f :=
    hderiv_cont.norm.sub (continuous_const.inner hderiv_cont)
  have hf_nonneg : ∀ u, 0 ≤ f u := by
    intro u
    have := real_inner_le_norm v (deriv c u)
    rw [hvnorm, one_mul] at this
    simpa [hf] using sub_nonneg.mpr this
  have hinner_int : ∫ u in a..b, ⟪v, deriv c u⟫_ℝ = ‖c b - c a‖ := by
    have h1 := (innerSL ℝ v).intervalIntegral_comp_comm
      (hderiv_cont.intervalIntegrable a b
        (μ := MeasureTheory.volume))
    have h2 : ∫ u in a..b, ⟪v, deriv c u⟫_ℝ = ⟪v, c b - c a⟫_ℝ := by
      simpa [hFTC b] using h1
    rw [h2, hv, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hne : ‖c b - c a‖ ≠ 0 := norm_ne_zero_iff.mpr hsub
    field_simp
  have hint : ∫ u in a..b, f u = 0 := by
    rw [hf]
    rw [intervalIntegral.integral_sub (hderiv_cont.norm.intervalIntegrable a b)
      ((continuous_const.inner hderiv_cont).intervalIntegrable a b)]
    have hnorm_int : ∫ u in a..b, ‖deriv c u‖ = ‖c b - c a‖ := by
      rw [← hL, heq, hdist]
    rw [hnorm_int, hinner_int, sub_self]
  have hf0 : ∀ u ∈ Icc a b, f u = 0 :=
    eqOn_zero_of_intervalIntegral_eq_zero hf_cont hab'
      (fun u _ => hf_nonneg u) hint
  -- pointwise: `ċ = |ċ| v` on `[a, b]`
  have hdir : ∀ u ∈ Icc a b, deriv c u = ‖deriv c u‖ • v := by
    intro u hu
    have h3 : ⟪v, deriv c u⟫_ℝ = ‖v‖ * ‖deriv c u‖ := by
      have := hf0 u hu
      rw [hvnorm, one_mul]
      simp only [hf] at this
      linarith
    have h4 := inner_eq_norm_mul_iff_real.mp h3
    rw [hvnorm, one_smul] at h4
    exact h4.symm
  -- `c u − c a = (∫_a^u |ċ|) v` on `[a, b]`
  have hcu : ∀ u ∈ Icc a b, c u - c a = (∫ s in a..u, ‖deriv c s‖) • v := by
    intro u hu
    have hcongr : ∀ s ∈ Set.uIcc a u, deriv c s = ‖deriv c s‖ • v := by
      intro s hs
      rw [Set.uIcc_of_le hu.1] at hs
      exact hdir s ⟨hs.1, hs.2.trans hu.2⟩
    rw [← hFTC u, intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_smul_const]
  -- the segment parameter
  set m : ℝ := ∫ s in a..t, ‖deriv c s‖ with hm
  set L : ℝ := ∫ s in a..b, ‖deriv c s‖ with hLint
  have hLnorm : L = ‖c b - c a‖ := by rw [← hL, heq, hdist]
  have hLpos : 0 < L := hLnorm ▸ norm_pos_iff.mpr hsub
  have hm_nonneg : 0 ≤ m :=
    intervalIntegral.integral_nonneg ht.1 fun s _ => norm_nonneg _
  have hm_le : m ≤ L := by
    have hsplit : m + ∫ s in t..b, ‖deriv c s‖ = L := by
      rw [hm, hLint]
      exact intervalIntegral.integral_add_adjacent_intervals
        (hderiv_cont.norm.intervalIntegrable a t)
        (hderiv_cont.norm.intervalIntegrable t b)
    have htail : 0 ≤ ∫ s in t..b, ‖deriv c s‖ :=
      intervalIntegral.integral_nonneg ht.2 fun s _ => norm_nonneg _
    linarith
  -- conclude membership in the segment
  rw [segment_eq_image']
  refine ⟨m / L, ⟨by positivity, by
    rw [div_le_one hLpos]; exact hm_le⟩, ?_⟩
  have hcb : c b - c a = L • v := by
    rw [hLint]
    exact hcu b ⟨hab, le_refl b⟩
  show c a + (m / L) • (c b - c a) = c t
  rw [hcb, smul_smul, div_mul_cancel₀ m hLpos.ne']
  have := hcu t ht
  rw [← hm] at this
  rw [← this]
  abel

end Exercise19

/-! ## Exercise 1.6.20 — great circles minimize on the sphere -/

section Exercise20

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Eng.** The squared norm of a combination of two orthonormal vectors:
`‖s • p + t • v‖² = s² + t²`. -/
private theorem norm_sq_smul_add_smul {p v : E} (hp : ‖p‖ = 1) (hv : ‖v‖ = 1)
    (hpv : ⟪p, v⟫_ℝ = 0) (s t : ℝ) :
    ‖s • p + t • v‖ ^ 2 = s ^ 2 + t ^ 2 := by
  have hvp : ⟪v, p⟫_ℝ = 0 := (real_inner_comm p v).trans hpv
  rw [← real_inner_self_eq_norm_sq, inner_add_add_self]
  simp only [real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    hp, hv, hpv, hvp]
  ring

/-- **Eng.** A combination of orthonormal vectors with `s² + t² = 1` is a unit
vector. -/
private theorem norm_smul_add_smul_eq_one {p v : E} (hp : ‖p‖ = 1)
    (hv : ‖v‖ = 1) (hpv : ⟪p, v⟫_ℝ = 0) {s t : ℝ} (h : s ^ 2 + t ^ 2 = 1) :
    ‖s • p + t • v‖ = 1 := by
  have hsq : ‖s • p + t • v‖ ^ 2 = 1 := by
    rw [norm_sq_smul_add_smul hp hv hpv, h]
  nlinarith [norm_nonneg (s • p + t • v), sq_nonneg (‖s • p + t • v‖ - 1),
    sq_nonneg (‖s • p + t • v‖ + 1)]

/-- **Eng.** A differentiable curve of unit vectors is orthogonal to its own
velocity: differentiating `⟪c, c⟫ = 1` gives `2 ⟪c, ċ⟫ = 0`. -/
theorem inner_deriv_eq_zero_of_norm_eq_one {c : ℝ → E}
    (hc : Differentiable ℝ c) (hsphere : ∀ t, ‖c t‖ = 1) (t : ℝ) :
    ⟪c t, deriv c t⟫_ℝ = 0 := by
  have hd : HasDerivAt (fun s => ⟪c s, c s⟫_ℝ)
      (⟪c t, deriv c t⟫_ℝ + ⟪deriv c t, c t⟫_ℝ) t :=
    HasDerivAt.inner ℝ (hc t).hasDerivAt (hc t).hasDerivAt
  have hconst : (fun s => ⟪c s, c s⟫_ℝ) = fun _ => (1 : ℝ) := by
    funext s
    rw [real_inner_self_eq_norm_sq, hsphere s, one_pow]
  have h0 : deriv (fun s => ⟪c s, c s⟫_ℝ) t = 0 := by
    rw [hconst]
    exact deriv_const t 1
  have hzero := hd.deriv
  rw [h0] at hzero
  have hcomm : ⟪deriv c t, c t⟫_ℝ = ⟪c t, deriv c t⟫_ℝ := real_inner_comm _ _
  linarith [hzero, hcomm]

/-- **Eng.** The radial-derivative bound on the sphere: for a curve `c` on
`Sⁿ` and a unit vector `p`, the derivative of the height `⟪p, c t⟫` is
bounded by `√(1 − ⟪p, c t⟫²) |ċ|` — Cauchy–Schwarz against the component of
`p` tangential to the sphere at `c t`. -/
theorem abs_inner_deriv_le_of_norm_eq_one {p : E} (hp : ‖p‖ = 1) {c : ℝ → E}
    (hc : Differentiable ℝ c) (hsphere : ∀ t, ‖c t‖ = 1) (t : ℝ) :
    |⟪p, deriv c t⟫_ℝ| ≤ Real.sqrt (1 - ⟪p, c t⟫_ℝ ^ 2) * ‖deriv c t‖ := by
  set u : ℝ := ⟪p, c t⟫_ℝ with hu
  have horth : ⟪c t, deriv c t⟫_ℝ = 0 :=
    inner_deriv_eq_zero_of_norm_eq_one hc hsphere t
  have hsplit : ⟪p, deriv c t⟫_ℝ = ⟪p - u • c t, deriv c t⟫_ℝ := by
    rw [inner_sub_left, real_inner_smul_left, horth]
    ring
  have hnorm_sq : ‖p - u • c t‖ ^ 2 = 1 - u ^ 2 := by
    have hcp : ⟪c t, p⟫_ℝ = u := (real_inner_comm p (c t)).trans hu.symm
    rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self]
    simp only [real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, hsphere t, hp, hcp, ← hu]
    ring
  have hnorm : ‖p - u • c t‖ = Real.sqrt (1 - u ^ 2) := by
    rw [← hnorm_sq]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  calc |⟪p, deriv c t⟫_ℝ| = |⟪p - u • c t, deriv c t⟫_ℝ| := by rw [hsplit]
    _ ≤ ‖p - u • c t‖ * ‖deriv c t‖ := abs_real_inner_le_norm _ _
    _ = Real.sqrt (1 - u ^ 2) * ‖deriv c t‖ := by rw [hnorm]

/-- **Math.** **Spherical distance bounds arc length from below**: for a
smooth curve `c` on the unit sphere (`‖c t‖ = 1`), the angle between the
endpoints bounds the (ambient = induced, Exercise 1.6.17) arc length:
`arccos ⟪c a, c b⟫ ≤ L(c)|_a^b`.

The proof avoids the poles of the radial coordinate `arccos ⟪c a, c t⟫`
(where `c t = ± c a` and `arccos` fails to be differentiable) by comparing
with the **mollified radial coordinate** `f_ε(t) = arccos (⟪c a, c t⟫/(1+ε))`,
which is differentiable for every `ε > 0` with `|f_ε'| ≤ |ċ|` — by
Cauchy–Schwarz against the tangential part of `c a`
(`abs_inner_deriv_le_of_norm_eq_one`) and `1 − u² ≤ (1+ε)² − u²`; the
fundamental theorem of calculus integrates this to
`f_ε(b) − f_ε(a) ≤ L(c)|_a^b`, and `ε → 0⁺` recovers the claim. -/
theorem arccos_inner_le_arcLength {c : ℝ → E} (hc : ContDiff ℝ ∞ c)
    {a b : ℝ} (hab : a ≤ b) (hsphere : ∀ t, ‖c t‖ = 1) :
    Real.arccos ⟪c a, c b⟫_ℝ ≤ arcLength (innerProductSpaceMetric E) c a b := by
  have hcd : Differentiable ℝ c := hc.differentiable (by simp)
  have hderiv_cont : Continuous (deriv c) := hc.continuous_deriv (by simp)
  have hp : ‖c a‖ = 1 := hsphere a
  -- the radial height `u t = ⟪c a, c t⟫` and its properties
  set u : ℝ → ℝ := fun t => ⟪c a, c t⟫_ℝ with hu_def
  have hu_deriv : ∀ t, HasDerivAt u ⟪c a, deriv c t⟫_ℝ t := by
    intro t
    have h1 := ((innerSL ℝ (c a)).hasFDerivAt (x := c t)).comp_hasDerivAt t
      (hcd t).hasDerivAt
    simpa using h1
  have hu'_cont : Continuous fun t => ⟪c a, deriv c t⟫_ℝ :=
    continuous_const.inner hderiv_cont
  have hu_cont : Continuous u := continuous_const.inner hcd.continuous
  have hu_bound : ∀ t, |u t| ≤ 1 := by
    intro t
    have h := abs_real_inner_le_norm (c a) (c t)
    rw [hp, hsphere t, one_mul] at h
    exact h
  have hu'_bound : ∀ t,
      |⟪c a, deriv c t⟫_ℝ| ≤ Real.sqrt (1 - u t ^ 2) * ‖deriv c t‖ :=
    fun t => abs_inner_deriv_le_of_norm_eq_one hp hcd hsphere t
  have hL : arcLength (innerProductSpaceMetric E) c a b
      = ∫ t in a..b, ‖deriv c t‖ := arcLength_eq_integral_norm_deriv c a b
  -- the mollified estimate, for every `ε > 0`
  have key : ∀ ε : ℝ, 0 < ε →
      Real.arccos (u b / (1 + ε)) - Real.arccos (u a / (1 + ε))
        ≤ ∫ t in a..b, ‖deriv c t‖ := by
    intro ε hε
    have hε1 : (0 : ℝ) < 1 + ε := by linarith
    set f' : ℝ → ℝ := fun t =>
      -(1 / Real.sqrt (1 - (u t / (1 + ε)) ^ 2))
        * (⟪c a, deriv c t⟫_ℝ / (1 + ε)) with hf'_def
    have harg_lt : ∀ t, |u t / (1 + ε)| < 1 := by
      intro t
      rw [abs_div, abs_of_pos hε1, div_lt_one hε1]
      exact lt_of_le_of_lt (hu_bound t) (by linarith)
    have hD_pos : ∀ t, 0 < 1 - (u t / (1 + ε)) ^ 2 := by
      intro t
      obtain ⟨h1, h2⟩ := abs_lt.mp (harg_lt t)
      nlinarith
    have hsqrt_pos : ∀ t, 0 < Real.sqrt (1 - (u t / (1 + ε)) ^ 2) :=
      fun t => Real.sqrt_pos.mpr (hD_pos t)
    have hf_deriv : ∀ t,
        HasDerivAt (fun s => Real.arccos (u s / (1 + ε))) (f' t) t := by
      intro t
      have h1 : HasDerivAt (fun s => u s / (1 + ε))
          (⟪c a, deriv c t⟫_ℝ / (1 + ε)) t := (hu_deriv t).div_const _
      have hne1 : u t / (1 + ε) ≠ -1 := by
        intro h
        have := harg_lt t
        rw [h] at this
        simp at this
      have hne2 : u t / (1 + ε) ≠ 1 := by
        intro h
        have := harg_lt t
        rw [h] at this
        simp at this
      have hcomp := HasDerivAt.comp t (Real.hasDerivAt_arccos hne1 hne2) h1
      simpa [Function.comp, hf'_def] using hcomp
    -- the pointwise speed bound `|f_ε'| ≤ |ċ|`
    have hf'_bound : ∀ t, |f' t| ≤ ‖deriv c t‖ := by
      intro t
      have habs : |f' t| = |⟪c a, deriv c t⟫_ℝ|
          / ((1 + ε) * Real.sqrt (1 - (u t / (1 + ε)) ^ 2)) := by
        simp only [hf'_def]
        rw [abs_mul, abs_neg, abs_div, abs_div, abs_one, abs_of_pos hε1,
          abs_of_pos (hsqrt_pos t)]
        rw [div_mul_div_comm, one_mul, mul_comm]
      rw [habs, div_le_iff₀ (mul_pos hε1 (hsqrt_pos t))]
      have hfactor : (1 + ε) * Real.sqrt (1 - (u t / (1 + ε)) ^ 2)
          = Real.sqrt ((1 + ε) ^ 2 - u t ^ 2) := by
        have h2 : (1 + ε) ^ 2 - u t ^ 2
            = (1 + ε) ^ 2 * (1 - (u t / (1 + ε)) ^ 2) := by
          field_simp
        rw [h2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hε1.le]
      have hmono : Real.sqrt (1 - u t ^ 2)
          ≤ Real.sqrt ((1 + ε) ^ 2 - u t ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith
      calc |⟪c a, deriv c t⟫_ℝ|
          ≤ Real.sqrt (1 - u t ^ 2) * ‖deriv c t‖ := hu'_bound t
        _ ≤ Real.sqrt ((1 + ε) ^ 2 - u t ^ 2) * ‖deriv c t‖ :=
            mul_le_mul_of_nonneg_right hmono (norm_nonneg _)
        _ = ‖deriv c t‖ * ((1 + ε) * Real.sqrt (1 - (u t / (1 + ε)) ^ 2)) := by
            rw [hfactor]; ring
    -- continuity of the mollified derivative
    have hf'_cont : Continuous f' := by
      apply Continuous.mul
      · apply Continuous.neg
        apply Continuous.div continuous_const
        · exact Real.continuous_sqrt.comp
            (continuous_const.sub ((hu_cont.div_const _).pow 2))
        · exact fun t => (hsqrt_pos t).ne'
      · exact hu'_cont.div_const _
    -- fundamental theorem of calculus and comparison
    have hFTC : ∫ t in a..b, f' t
        = Real.arccos (u b / (1 + ε)) - Real.arccos (u a / (1 + ε)) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hf_deriv t) (hf'_cont.intervalIntegrable a b)
    calc Real.arccos (u b / (1 + ε)) - Real.arccos (u a / (1 + ε))
        = ∫ t in a..b, f' t := hFTC.symm
      _ ≤ |∫ t in a..b, f' t| := le_abs_self _
      _ ≤ ∫ t in a..b, |f' t| :=
          intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ t in a..b, ‖deriv c t‖ :=
          intervalIntegral.integral_mono_on hab
            (hf'_cont.abs.intervalIntegrable a b)
            (hderiv_cont.norm.intervalIntegrable a b)
            (fun t _ => hf'_bound t)
  -- pass to the limit `ε → 0⁺`
  have hlim : Filter.Tendsto (fun ε : ℝ =>
      Real.arccos (u b / (1 + ε)) - Real.arccos (u a / (1 + ε)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.arccos (u b) - Real.arccos (u a))) := by
    have hconta : ContinuousAt (fun ε : ℝ =>
        Real.arccos (u b / (1 + ε)) - Real.arccos (u a / (1 + ε))) 0 := by
      have hden : ContinuousAt (fun ε : ℝ => 1 + ε) 0 :=
        continuousAt_const.add continuousAt_id
      have hden_ne : (1 : ℝ) + 0 ≠ 0 := by norm_num
      exact ((Real.continuous_arccos.continuousAt).comp
          (continuousAt_const.div hden hden_ne)).sub
        ((Real.continuous_arccos.continuousAt).comp
          (continuousAt_const.div hden hden_ne))
    have h0 : Real.arccos (u b / (1 + 0)) - Real.arccos (u a / (1 + 0))
        = Real.arccos (u b) - Real.arccos (u a) := by norm_num
    exact h0 ▸ hconta.continuousWithinAt.tendsto
  have hfinal : Real.arccos (u b) - Real.arccos (u a)
      ≤ ∫ t in a..b, ‖deriv c t‖ :=
    le_of_tendsto hlim
      (Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => key ε hε)
  have hua : u a = 1 := by
    rw [hu_def]
    simp only [real_inner_self_eq_norm_sq, hp, one_pow]
  rw [hL]
  calc Real.arccos ⟪c a, c b⟫_ℝ
      = Real.arccos (u b) - Real.arccos (u a) := by
        rw [hua, Real.arccos_one, sub_zero]
    _ ≤ ∫ t in a..b, ‖deriv c t‖ := hfinal

/-- **Eng.** Equality in the **spherical triangle inequality**: a unit vector
`x` with `arccos ⟪p, x⟫ + arccos ⟪x, q⟫ ≤ r₀`, where
`q = cos r₀ • p + sin r₀ • v₀` (`p, v₀` orthonormal, `0 < r₀ < π`), lies on
the great-circle arc from `p` to `q`:
`x = cos s • p + sin s • v₀` with `s = arccos ⟪p, x⟫ ∈ [0, r₀]`. -/
theorem eq_greatCircle_of_arccos_add_arccos_le {p v₀ x : E}
    (hp : ‖p‖ = 1) (hv : ‖v₀‖ = 1) (hpv : ⟪p, v₀⟫_ℝ = 0) {r₀ : ℝ}
    (hr : r₀ ∈ Ioo 0 Real.pi) (hx : ‖x‖ = 1)
    (hsum : Real.arccos ⟪p, x⟫_ℝ
      + Real.arccos ⟪x, Real.cos r₀ • p + Real.sin r₀ • v₀⟫_ℝ ≤ r₀) :
    Real.arccos ⟪p, x⟫_ℝ ∈ Icc 0 r₀ ∧
    x = Real.cos (Real.arccos ⟪p, x⟫_ℝ) • p
        + Real.sin (Real.arccos ⟪p, x⟫_ℝ) • v₀ := by
  have hpp : ⟪p, p⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hp, one_pow]
  set q : E := Real.cos r₀ • p + Real.sin r₀ • v₀ with hq_def
  set α : ℝ := Real.arccos ⟪p, x⟫_ℝ with hα_def
  set β : ℝ := Real.arccos ⟪x, q⟫_ℝ with hβ_def
  have hα_nonneg : 0 ≤ α := Real.arccos_nonneg _
  have hβ_nonneg : 0 ≤ β := Real.arccos_nonneg _
  have hα_le : α ≤ r₀ := by linarith [hβ_nonneg, hsum]
  refine ⟨⟨hα_nonneg, hα_le⟩, ?_⟩
  -- bounds on the inner products
  have hpx_bound : |⟪p, x⟫_ℝ| ≤ 1 := by
    have h := abs_real_inner_le_norm p x
    rw [hp, hx, one_mul] at h
    exact h
  have hcosα : Real.cos α = ⟪p, x⟫_ℝ :=
    Real.cos_arccos (neg_le_of_abs_le hpx_bound) (le_of_abs_le hpx_bound)
  have hsinα : Real.sin α = Real.sqrt (1 - ⟪p, x⟫_ℝ ^ 2) :=
    Real.sin_arccos _
  have hsinα_nonneg : 0 ≤ Real.sin α := by
    rw [hsinα]; exact Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hsinα_nonneg with hsin0 | hsin_pos
  · -- `sin α = 0` with `0 ≤ α ≤ r₀ < π` forces `α = 0`, hence `x = p`
    have hα0 : α = 0 := by
      by_contra hne
      have hαpos : 0 < α := lt_of_le_of_ne hα_nonneg (Ne.symm hne)
      have : 0 < Real.sin α :=
        Real.sin_pos_of_pos_of_lt_pi hαpos (lt_of_le_of_lt hα_le hr.2)
      linarith [hsin0]
    have hpx1 : ⟪p, x⟫_ℝ = 1 := by
      have h1 : (1 : ℝ) ≤ ⟪p, x⟫_ℝ := Real.arccos_eq_zero.mp (hα_def ▸ hα0)
      linarith [le_of_abs_le hpx_bound]
    have hxp : x = p := by
      have hxp_inner : ⟪x, p⟫_ℝ = 1 := (real_inner_comm p x).trans hpx1
      have hsq0 : ‖x - p‖ ^ 2 = 0 := by
        rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self,
          real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hx, hp,
          hpx1, hxp_inner]
        ring
      have : ‖x - p‖ = 0 := sq_eq_zero_iff.mp hsq0
      rw [sub_eq_zero.mp (norm_eq_zero.mp this)]
    rw [hα0, hxp]
    simp
  · -- main case: `sin α > 0`, decompose `x = cos α • p + sin α • w`
    have hsinr₀_pos : 0 < Real.sin r₀ := Real.sin_pos_of_pos_of_lt_pi hr.1 hr.2
    set t : ℝ := ⟪p, x⟫_ℝ with ht_def
    have hxts : ‖x - t • p‖ ^ 2 = 1 - t ^ 2 := by
      have hxp_inner : ⟪x, p⟫_ℝ = t := (real_inner_comm p x).trans ht_def.symm
      rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self]
      simp only [real_inner_smul_left, real_inner_smul_right,
        real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow,
        sq_abs, hx, hp, hxp_inner, ← ht_def]
      ring
    have hxt_norm : ‖x - t • p‖ = Real.sin α := by
      rw [hsinα, ← hxts]
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    set w : E := (Real.sin α)⁻¹ • (x - t • p) with hw_def
    have hw_norm : ‖w‖ = 1 := by
      rw [hw_def, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hsin_pos, hxt_norm, inv_mul_cancel₀ hsin_pos.ne']
    have hpw : ⟪p, w⟫_ℝ = 0 := by
      rw [hw_def, real_inner_smul_right, inner_sub_right,
        real_inner_smul_right, hpp, ← ht_def]
      ring
    have hx_decomp : x = Real.cos α • p + Real.sin α • w := by
      rw [hw_def, smul_smul, mul_inv_cancel₀ hsin_pos.ne', one_smul, hcosα]
      abel
    -- compute `⟪x, q⟫ = cos α cos r₀ + sin α sin r₀ ⟪w, v₀⟫`
    have hwp : ⟪w, p⟫_ℝ = 0 := (real_inner_comm p w).trans hpw
    have hxq : ⟪x, q⟫_ℝ = Real.cos α * Real.cos r₀
        + Real.sin α * Real.sin r₀ * ⟪w, v₀⟫_ℝ := by
      rw [hx_decomp, hq_def]
      simp only [inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, hpp, hpv, hwp]
      ring
    -- `β ≤ r₀ − α` and cosine monotonicity give `cos (r₀ − α) ≤ ⟪x, q⟫`
    have hβ_le : β ≤ r₀ - α := by linarith [hsum]
    have hrα_le_pi : r₀ - α ≤ Real.pi := by
      have := hr.2
      linarith [hα_nonneg]
    have hcosβ : Real.cos β = ⟪x, q⟫_ℝ := by
      have hxq_bound : |⟪x, q⟫_ℝ| ≤ 1 := by
        have h := abs_real_inner_le_norm x q
        have hq_norm : ‖q‖ = 1 := by
          rw [hq_def]
          exact norm_smul_add_smul_eq_one hp hv hpv
            (Real.cos_sq_add_sin_sq r₀)
        rw [hx, hq_norm, one_mul] at h
        exact h
      exact Real.cos_arccos (neg_le_of_abs_le hxq_bound)
        (le_of_abs_le hxq_bound)
    have hcos_mono : Real.cos (r₀ - α) ≤ Real.cos β :=
      Real.cos_le_cos_of_nonneg_of_le_pi hβ_nonneg hrα_le_pi hβ_le
    have hcos_sub : Real.cos (r₀ - α)
        = Real.cos r₀ * Real.cos α + Real.sin r₀ * Real.sin α :=
      Real.cos_sub r₀ α
    -- conclude `⟪w, v₀⟫ ≥ 1`, hence `w = v₀`
    have hwv_ge : 1 ≤ ⟪w, v₀⟫_ℝ := by
      rw [hcosβ, hxq] at hcos_mono
      rw [hcos_sub] at hcos_mono
      have hprod_pos : 0 < Real.sin α * Real.sin r₀ :=
        mul_pos hsin_pos hsinr₀_pos
      nlinarith [hcos_mono, hprod_pos]
    have hwv_le : ⟪w, v₀⟫_ℝ ≤ 1 := by
      have h := real_inner_le_norm w v₀
      rw [hw_norm, hv, one_mul] at h
      exact h
    have hwv : ⟪w, v₀⟫_ℝ = 1 := le_antisymm hwv_le hwv_ge
    have hw_eq : w = v₀ := by
      have hvw : ⟪v₀, w⟫_ℝ = 1 := (real_inner_comm w v₀).trans hwv
      have hsq0 : ‖w - v₀‖ ^ 2 = 0 := by
        rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self,
          real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hw_norm, hv,
          hwv, hvw]
        ring
      have : ‖w - v₀‖ = 0 := sq_eq_zero_iff.mp hsq0
      rw [sub_eq_zero.mp (norm_eq_zero.mp this)]
    rw [hx_decomp, hw_eq]

/-- **Math.** Exercise 1.6.20 (1): for unit vectors `p ⊥ v`, the **great
circle** `γ(t) = p cos t + v sin t` is a unit-speed curve on `Sⁿ` starting at
`p` with initial velocity `v`; its derivative is `γ'(t) = −p sin t + v cos t`
and its arc length over `[a, b]` is `b − a` (unit speed). -/
theorem exercise1_6_20_greatCircle {p v : E} (hp : ‖p‖ = 1) (hv : ‖v‖ = 1)
    (hpv : ⟪p, v⟫_ℝ = 0) :
    (∀ t, ‖Real.cos t • p + Real.sin t • v‖ = 1) ∧
    Real.cos 0 • p + Real.sin 0 • v = p ∧
    (∀ t, HasDerivAt (fun s => Real.cos s • p + Real.sin s • v)
      (-Real.sin t • p + Real.cos t • v) t) ∧
    deriv (fun s => Real.cos s • p + Real.sin s • v) 0 = v ∧
    (∀ t, ‖deriv (fun s => Real.cos s • p + Real.sin s • v) t‖ = 1) ∧
    (∀ a b : ℝ, arcLength (innerProductSpaceMetric E)
      (fun s => Real.cos s • p + Real.sin s • v) a b = b - a) := by
  have hderiv : ∀ t, HasDerivAt (fun s => Real.cos s • p + Real.sin s • v)
      (-Real.sin t • p + Real.cos t • v) t := by
    intro t
    exact ((Real.hasDerivAt_cos t).smul_const p).add
      ((Real.hasDerivAt_sin t).smul_const v)
  have hnorm : ∀ t, ‖Real.cos t • p + Real.sin t • v‖ = 1 := fun t =>
    norm_smul_add_smul_eq_one hp hv hpv (Real.cos_sq_add_sin_sq t)
  have hspeed : ∀ t, ‖deriv (fun s => Real.cos s • p + Real.sin s • v) t‖ = 1 := by
    intro t
    rw [(hderiv t).deriv]
    refine norm_smul_add_smul_eq_one hp hv hpv ?_
    rw [neg_pow]
    simpa using Real.sin_sq_add_cos_sq t
  refine ⟨hnorm, by simp, hderiv, by simpa using (hderiv 0).deriv, hspeed, ?_⟩
  intro a b
  rw [arcLength_eq_integral_norm_deriv]
  simp only [hspeed]
  simp

/-- **Math.** Exercise 1.6.20 (2): with `p` a unit vector, the polar map
`G(r, w) = p cos r + w sin r` is smooth on `ℝ × E` and restricts to a
bijection `(0, π) × S^{n-1} → Sⁿ − {±p}` (where
`S^{n-1} = {w | w ⊥ p, ‖w‖ = 1}`), whose inverse
`x ↦ (arccos⟪p, x⟫, (x − ⟪p, x⟫p)/sin(arccos⟪p, x⟫))` is smooth on the open
set `{x | |⟪p, x⟫| < 1}` ⊇ `Sⁿ − {±p}` — this is the diffeomorphism content
of the exercise, expressed ambiently (the sets carry the subspace smooth
structure via these charts). -/
theorem exercise1_6_20_polar {p : E} (hp : ‖p‖ = 1) :
    ContDiff ℝ ∞ (fun q : ℝ × E => Real.cos q.1 • p + Real.sin q.1 • q.2) ∧
    Set.BijOn (fun q : ℝ × E => Real.cos q.1 • p + Real.sin q.1 • q.2)
      (Ioo 0 Real.pi ×ˢ {w : E | ⟪p, w⟫_ℝ = 0 ∧ ‖w‖ = 1})
      {x : E | ‖x‖ = 1 ∧ x ≠ p ∧ x ≠ -p} ∧
    ContDiffOn ℝ ∞ (fun x : E =>
        ((Real.arccos ⟪p, x⟫_ℝ : ℝ),
          (Real.sin (Real.arccos ⟪p, x⟫_ℝ))⁻¹ • (x - ⟪p, x⟫_ℝ • p)))
      {x : E | |⟪p, x⟫_ℝ| < 1} ∧
    ∀ q ∈ Ioo 0 Real.pi ×ˢ {w : E | ⟪p, w⟫_ℝ = 0 ∧ ‖w‖ = 1},
      ((Real.arccos ⟪p, Real.cos q.1 • p + Real.sin q.1 • q.2⟫_ℝ : ℝ),
        (Real.sin (Real.arccos ⟪p, Real.cos q.1 • p + Real.sin q.1 • q.2⟫_ℝ))⁻¹ •
          (Real.cos q.1 • p + Real.sin q.1 • q.2
            - ⟪p, Real.cos q.1 • p + Real.sin q.1 • q.2⟫_ℝ • p)) = q := by
  have hpp : ⟪p, p⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hp, one_pow]
  -- the first coordinate of the inner product with `p`
  have hinner : ∀ (r : ℝ) (w : E), ⟪p, w⟫_ℝ = 0 →
      ⟪p, Real.cos r • p + Real.sin r • w⟫_ℝ = Real.cos r := by
    intro r w hw
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hpp, hw]
    ring
  constructor
  · -- smoothness of `G`
    exact ((Real.contDiff_cos.comp contDiff_fst).smul contDiff_const).add
      ((Real.contDiff_sin.comp contDiff_fst).smul contDiff_snd)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- MapsTo
    rintro ⟨r, w⟩ ⟨hr, hw, hwn⟩
    have hmem : ‖Real.cos r • p + Real.sin r • w‖ = 1 :=
      norm_smul_add_smul_eq_one hp hwn hw (Real.cos_sq_add_sin_sq r)
    have hcos_lt : Real.cos r < 1 := by
      have := Real.strictAntiOn_cos ⟨le_refl 0, Real.pi_pos.le⟩
        ⟨hr.1.le, hr.2.le⟩ hr.1
      simpa using this
    have hcos_gt : -1 < Real.cos r := by
      have := Real.strictAntiOn_cos ⟨hr.1.le, hr.2.le⟩
        ⟨Real.pi_pos.le, le_refl Real.pi⟩ hr.2
      simpa using this
    refine ⟨hmem, fun hxp => ?_, fun hxp => ?_⟩
    · have hxp' : Real.cos r • p + Real.sin r • w = p := hxp
      have := hinner r w hw
      rw [hxp', hpp] at this
      linarith
    · have hxp' : Real.cos r • p + Real.sin r • w = -p := hxp
      have := hinner r w hw
      rw [hxp', inner_neg_right, hpp] at this
      linarith
  · -- InjOn
    rintro ⟨r, w⟩ ⟨hr, hw, hwn⟩ ⟨r', w'⟩ ⟨hr', hw', hwn'⟩ heq
    have heq' : Real.cos r • p + Real.sin r • w
        = Real.cos r' • p + Real.sin r' • w' := heq
    have hcos : Real.cos r = Real.cos r' := by
      have h1 := hinner r w hw
      have h2 := hinner r' w' hw'
      rw [heq'] at h1
      rw [h1] at h2
      exact h2
    have hrr : r = r' := Real.injOn_cos ⟨hr.1.le, hr.2.le⟩ ⟨hr'.1.le, hr'.2.le⟩ hcos
    have hsin_ne : Real.sin r ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi hr.1 hr.2).ne'
    have hw_eq : w = w' := by
      have h3 : Real.sin r • w = Real.sin r • w' := by
        have h5 := heq'
        rw [← hrr] at h5
        have h4 := congrArg (fun x => x - Real.cos r • p) h5
        simpa using h4
      have h6 : Real.sin r • (w - w') = 0 := by
        rw [smul_sub, h3, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h6).resolve_left hsin_ne)
    rw [Prod.ext_iff]
    exact ⟨hrr, hw_eq⟩
  · -- SurjOn
    rintro x ⟨hx1, hxp, hxnp⟩
    have hpx_lt : ⟪p, x⟫_ℝ < 1 := by
      by_contra hle
      push_neg at hle
      have hcs : ⟪p, x⟫_ℝ ≤ 1 := by
        have := real_inner_le_norm p x
        rw [hp, hx1] at this
        simpa using this
      have hpx1 : ⟪p, x⟫_ℝ = 1 := le_antisymm hcs hle
      have hxp1 : ⟪x, p⟫_ℝ = 1 := (real_inner_comm x p).symm.trans hpx1
      have hsq0 : ‖p - x‖ ^ 2 = 0 := by
        rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self, hpp,
          real_inner_self_eq_norm_sq, hx1]
        linarith [hpx1, hxp1]
      have hzero : p - x = 0 := by
        have hn : ‖p - x‖ = 0 := by nlinarith [norm_nonneg (p - x)]
        exact norm_eq_zero.mp hn
      exact hxp (sub_eq_zero.mp hzero).symm
    have hpx_gt : -1 < ⟪p, x⟫_ℝ := by
      by_contra hle
      push_neg at hle
      have hcs : -1 ≤ ⟪p, x⟫_ℝ := by
        have := abs_real_inner_le_norm p x
        rw [hp, hx1] at this
        have := (abs_le.mp (by simpa using this)).1
        exact this
      have hpx1 : ⟪p, x⟫_ℝ = -1 := le_antisymm hle hcs
      have hxp1 : ⟪x, p⟫_ℝ = -1 := (real_inner_comm x p).symm.trans hpx1
      have hsum : ‖p + x‖ ^ 2 = 0 := by
        rw [← real_inner_self_eq_norm_sq, inner_add_add_self, hpp,
          real_inner_self_eq_norm_sq, hx1]
        linarith [hpx1, hxp1]
      have hzero : p + x = 0 := by
        have hn : ‖p + x‖ = 0 := by nlinarith [norm_nonneg (p + x)]
        exact norm_eq_zero.mp hn
      exact hxnp (by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hzero)
    set t := ⟪p, x⟫_ℝ with ht_def
    set r := Real.arccos t with hr_def
    have hr_mem : r ∈ Ioo 0 Real.pi :=
      ⟨Real.arccos_pos.mpr hpx_lt, Real.arccos_lt_pi.mpr hpx_gt⟩
    have hcos_r : Real.cos r = t := Real.cos_arccos hpx_gt.le hpx_lt.le
    have hsin_r : Real.sin r = Real.sqrt (1 - t ^ 2) := Real.sin_arccos t
    have ht_sq : t ^ 2 < 1 := by
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - t)
        (by linarith : (0 : ℝ) < 1 + t)]
    have hsin_pos : 0 < Real.sin r := by
      rw [hsin_r]
      apply Real.sqrt_pos.mpr
      linarith
    set w := (Real.sin r)⁻¹ • (x - t • p) with hw_def
    have hpw : ⟪p, w⟫_ℝ = 0 := by
      rw [hw_def, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
        hpp, ht_def]
      ring
    have hxts : ‖x - t • p‖ ^ 2 = 1 - t ^ 2 := by
      have hxp_inner : ⟪x, p⟫_ℝ = t := (real_inner_comm x p).symm.trans ht_def.symm
      rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self]
      simp only [real_inner_smul_left, real_inner_smul_right,
        real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow,
        sq_abs, hx1, hp, hxp_inner, ← ht_def]
      ring
    have hwn : ‖w‖ = 1 := by
      rw [hw_def, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hsin_pos]
      have hxn : ‖x - t • p‖ = Real.sin r := by
        rw [hsin_r]
        rw [show (1 : ℝ) - t ^ 2 = ‖x - t • p‖ ^ 2 from hxts.symm]
        exact (Real.sqrt_sq (norm_nonneg _)).symm
      rw [hxn, inv_mul_cancel₀ hsin_pos.ne']
    refine ⟨(r, w), ⟨hr_mem, hpw, hwn⟩, ?_⟩
    show Real.cos r • p + Real.sin r • w = x
    rw [hw_def, smul_smul, mul_inv_cancel₀ hsin_pos.ne', one_smul, hcos_r]
    abel
  · -- smoothness of the inverse on the open set `{|⟪p, x⟫| < 1}`
    intro x hx
    have hx' : |⟪p, x⟫_ℝ| < 1 := hx
    have hne1 : ⟪p, x⟫_ℝ ≠ 1 := by
      intro h
      rw [h] at hx'
      simp at hx'
    have hne1' : ⟪p, x⟫_ℝ ≠ -1 := by
      intro h
      rw [h] at hx'
      simp at hx'
    have hinner_cd : ContDiffAt ℝ ∞ (fun y : E => ⟪p, y⟫_ℝ) x :=
      (contDiff_const.inner ℝ contDiff_id).contDiffAt
    have harccos : ContDiffAt ℝ ∞ (fun y : E => Real.arccos ⟪p, y⟫_ℝ) x :=
      (Real.contDiffAt_arccos hne1' hne1).comp x hinner_cd
    have hsin_ne : Real.sin (Real.arccos ⟪p, x⟫_ℝ) ≠ 0 := by
      rw [Real.sin_arccos]
      refine (Real.sqrt_pos.mpr ?_).ne'
      nlinarith [sq_abs ⟪p, x⟫_ℝ, abs_nonneg ⟪p, x⟫_ℝ]
    have hsecond : ContDiffAt ℝ ∞ (fun y : E =>
        (Real.sin (Real.arccos ⟪p, y⟫_ℝ))⁻¹ • (y - ⟪p, y⟫_ℝ • p)) x := by
      refine ContDiffAt.smul ?_ ?_
      · exact (Real.contDiff_sin.contDiffAt.comp x harccos).inv hsin_ne
      · exact contDiffAt_id.sub (hinner_cd.smul contDiffAt_const)
    exact (harccos.prodMk hsecond).contDiffWithinAt
  · -- left inverse on the box
    rintro ⟨r, w⟩ ⟨hr, hw, hwn⟩
    have h1 : ⟪p, Real.cos r • p + Real.sin r • w⟫_ℝ = Real.cos r :=
      hinner r w hw
    have harc : Real.arccos (Real.cos r) = r :=
      Real.arccos_cos hr.1.le hr.2.le
    have hsin_ne : Real.sin r ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi hr.1 hr.2).ne'
    refine Prod.ext ?_ ?_
    · show Real.arccos ⟪p, Real.cos r • p + Real.sin r • w⟫_ℝ = r
      rw [h1, harc]
    · show (Real.sin (Real.arccos ⟪p, Real.cos r • p + Real.sin r • w⟫_ℝ))⁻¹ •
          (Real.cos r • p + Real.sin r • w
            - ⟪p, Real.cos r • p + Real.sin r • w⟫_ℝ • p) = w
      rw [h1, harc]
      have : Real.cos r • p + Real.sin r • w - Real.cos r • p
          = Real.sin r • w := by abel
      rw [this, smul_smul, inv_mul_cancel₀ hsin_ne, one_smul]

/-- **Math.** Exercise 1.6.20 (3): the **radial field**. At
`q = p cos r₀ + v₀ sin r₀` (`0 < r₀ < π`, `v₀ ⊥ p` unit), the coordinate
field `∂_r = F_*(∂_r)` is `∂F/∂r(r₀, v₀) = −p sin r₀ + v₀ cos r₀`, and it
coincides with the announced intrinsic formula
`(−p + (p ⋅ q) q)/√(1 − (p ⋅ q)²)`. -/
theorem exercise1_6_20_radialField {p v₀ : E} (hp : ‖p‖ = 1) (hv : ‖v₀‖ = 1)
    (hpv : ⟪p, v₀⟫_ℝ = 0) {r₀ : ℝ} (hr : r₀ ∈ Ioo 0 Real.pi) :
    deriv (fun r => Real.cos r • p + Real.sin r • v₀) r₀
      = -Real.sin r₀ • p + Real.cos r₀ • v₀ ∧
    (Real.sqrt (1 - ⟪p, Real.cos r₀ • p + Real.sin r₀ • v₀⟫_ℝ ^ 2))⁻¹ •
        (-p + ⟪p, Real.cos r₀ • p + Real.sin r₀ • v₀⟫_ℝ •
          (Real.cos r₀ • p + Real.sin r₀ • v₀))
      = -Real.sin r₀ • p + Real.cos r₀ • v₀ := by
  have hpp : ⟪p, p⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hp, one_pow]
  have hq : ⟪p, Real.cos r₀ • p + Real.sin r₀ • v₀⟫_ℝ = Real.cos r₀ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hpp, hpv]
    ring
  have hsin_pos : 0 < Real.sin r₀ := Real.sin_pos_of_pos_of_lt_pi hr.1 hr.2
  constructor
  · exact (((Real.hasDerivAt_cos r₀).smul_const p).add
      ((Real.hasDerivAt_sin r₀).smul_const v₀)).deriv
  · rw [hq]
    have hsqrt : Real.sqrt (1 - Real.cos r₀ ^ 2) = Real.sin r₀ := by
      rw [← Real.sin_sq]
      exact Real.sqrt_sq hsin_pos.le
    rw [hsqrt]
    have hs0 : Real.sin r₀ ≠ 0 := hsin_pos.ne'
    match_scalars
    · field_simp
      nlinarith [Real.sin_sq_add_cos_sq r₀]
    · field_simp

/-- **Math.** Exercise 1.6.20 (4): **great circles minimize**. For
`q = p cos r₀ + v₀ sin r₀` (`0 < r₀ < π`) and any smooth curve `c` on the
sphere (`‖c t‖ = 1`) from `p` to `q`, the (ambient = induced, Exercise
1.6.17) arc length satisfies `L(c) ≥ r₀`, with equality only if `c` stays on
the great-circle arc `{p cos s + v₀ sin s | s ∈ [0, r₀]}`. Hint of the text:
compare `L(c)` with `∫ ċ ⋅ ∂_r dt` and show `ċ ⋅ ∂_r = dr/dt`. -/
theorem exercise1_6_20_minimize {p v₀ : E} (hp : ‖p‖ = 1) (hv : ‖v₀‖ = 1)
    (hpv : ⟪p, v₀⟫_ℝ = 0) {r₀ : ℝ} (hr : r₀ ∈ Ioo 0 Real.pi)
    {c : ℝ → E} (hc : ContDiff ℝ ∞ c) {a b : ℝ} (hab : a ≤ b)
    (hsphere : ∀ t, ‖c t‖ = 1) (hca : c a = p)
    (hcb : c b = Real.cos r₀ • p + Real.sin r₀ • v₀) :
    r₀ ≤ arcLength (innerProductSpaceMetric E) c a b ∧
    (arcLength (innerProductSpaceMetric E) c a b = r₀ →
      ∀ t ∈ Icc a b, ∃ s ∈ Icc 0 r₀,
        c t = Real.cos s • p + Real.sin s • v₀) := by
  have hpp : ⟪p, p⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hp, one_pow]
  have hq_inner : ⟪p, Real.cos r₀ • p + Real.sin r₀ • v₀⟫_ℝ = Real.cos r₀ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hpp,
      hpv]
    ring
  have hderiv_cont : Continuous (deriv c) := hc.continuous_deriv (by simp)
  -- part (1): comparison with the (mollified) radial coordinate
  have h1 : r₀ ≤ arcLength (innerProductSpaceMetric E) c a b := by
    have h := arccos_inner_le_arcLength hc hab hsphere
    rw [hca, hcb, hq_inner, Real.arccos_cos hr.1.le hr.2.le] at h
    exact h
  refine ⟨h1, fun heq t ht => ?_⟩
  -- part (2): equality — split the length at `t` and use the equality case
  -- of the spherical triangle inequality
  have hsplit : arcLength (innerProductSpaceMetric E) c a t
      + arcLength (innerProductSpaceMetric E) c t b
      = arcLength (innerProductSpaceMetric E) c a b := by
    rw [arcLength_eq_integral_norm_deriv, arcLength_eq_integral_norm_deriv,
      arcLength_eq_integral_norm_deriv]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hderiv_cont.norm.intervalIntegrable a t)
      (hderiv_cont.norm.intervalIntegrable t b)
  have h2 := arccos_inner_le_arcLength hc ht.1 hsphere
  have h3 := arccos_inner_le_arcLength hc ht.2 hsphere
  rw [hca] at h2
  rw [hcb] at h3
  have hsum : Real.arccos ⟪p, c t⟫_ℝ
      + Real.arccos ⟪c t, Real.cos r₀ • p + Real.sin r₀ • v₀⟫_ℝ ≤ r₀ := by
    linarith [h2, h3, hsplit, heq]
  obtain ⟨hs_mem, hs_eq⟩ :=
    eq_greatCircle_of_arccos_add_arccos_le hp hv hpv hr (hsphere t) hsum
  exact ⟨Real.arccos ⟪p, c t⟫_ℝ, hs_mem, hs_eq⟩

/-- **Math.** Exercise 1.6.20 (5): **there is no Riemannian immersion from an
open subset of `ℝⁿ` into `Sⁿ`** (`n ≥ 2`). The immersion conditions are
stated pointwise on the open set `U` (`F` smooth, `DF` injective and
isometric into the induced metric of the unit sphere), following the
punctured/open-set representation used throughout this file.

Petersen suggests deducing this from the angle comparison of part (4) —
equilateral spherical triangles have angles `> π/3`, equilateral Euclidean
ones exactly `π/3`. That route needs the image of a straight segment under a
local isometry to be a *geodesic* of the sphere, which is Chapter 5 material.
`no_isometricImmersion_flat_to_sphere` proves the same statement inside
Chapter 1 instead, by differentiating the immersion identities three times:
they force `∂ᵢ∂ⱼ(ι ∘ F) = -δᵢⱼ (ι ∘ F)`, an overdetermined system whose
integrability condition fails for `n ≥ 2`. -/
theorem exercise1_6_20_no_immersion {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    (hn : 2 ≤ n) {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hne : U.Nonempty) (F : EuclideanSpace ℝ (Fin n) → sphere (0 : E) 1)
    (hFd : ∀ x ∈ U, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ F x)
    (hFinj : ∀ x ∈ U, Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) F x))
    (hFiso : ∀ x ∈ U, ∀ u v : EuclideanSpace ℝ (Fin n),
      ⟪u, v⟫_ℝ = (sphereMetricUnit (n := n) E).metricInner (F x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) F x u)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) F x v)) :
    False :=
  no_isometricImmersion_flat_to_sphere hn hU hne F hFd hFiso

/-- **Math.** **Exercise 1.6.20** (Petersen §1.6): geometry of the round
sphere `Sⁿ ⊂ ℝⁿ⁺¹` (ambient formulation, justified by Exercise 1.6.17 for the
isometric embedding `Sⁿ ↪ ℝⁿ⁺¹`):

1. great circles `p cos t + v sin t` are unit-speed curves
   (`exercise1_6_20_greatCircle`);
2. `F(r, v) = p cos r + v sin r` is a diffeomorphism
   `(0, π) × S^{n-1} → Sⁿ − {±p}` (`exercise1_6_20_polar`);
3. the radial field is
   `∂_r|_q = (−p + (p⋅q)q)/√(1 − (p⋅q)²) = −p sin r₀ + v₀ cos r₀`
   (`exercise1_6_20_radialField`);
4. every curve from `p` to `q = F(r₀, v₀)` has length `≥ r₀`, with equality
   only on the great circle (`exercise1_6_20_minimize`);
5. no open `U ⊂ ℝⁿ` immerses isometrically into `Sⁿ` for `n ≥ 2`
   (`exercise1_6_20_no_immersion`). -/
theorem exercise1_6_20 {n : ℕ} [Fact (finrank ℝ E = n + 1)] (hn : 2 ≤ n)
    {p v₀ : E} (hp : ‖p‖ = 1) (hv : ‖v₀‖ = 1) (hpv : ⟪p, v₀⟫_ℝ = 0)
    {r₀ : ℝ} (hr : r₀ ∈ Ioo 0 Real.pi) :
    ((∀ t, ‖Real.cos t • p + Real.sin t • v₀‖ = 1) ∧
      Real.cos 0 • p + Real.sin 0 • v₀ = p ∧
      deriv (fun s => Real.cos s • p + Real.sin s • v₀) 0 = v₀ ∧
      (∀ t, ‖deriv (fun s => Real.cos s • p + Real.sin s • v₀) t‖ = 1)) ∧
    Set.BijOn (fun q : ℝ × E => Real.cos q.1 • p + Real.sin q.1 • q.2)
      (Ioo 0 Real.pi ×ˢ {w : E | ⟪p, w⟫_ℝ = 0 ∧ ‖w‖ = 1})
      {x : E | ‖x‖ = 1 ∧ x ≠ p ∧ x ≠ -p} ∧
    ((Real.sqrt (1 - ⟪p, Real.cos r₀ • p + Real.sin r₀ • v₀⟫_ℝ ^ 2))⁻¹ •
        (-p + ⟪p, Real.cos r₀ • p + Real.sin r₀ • v₀⟫_ℝ •
          (Real.cos r₀ • p + Real.sin r₀ • v₀))
      = -Real.sin r₀ • p + Real.cos r₀ • v₀) ∧
    (∀ (c : ℝ → E), ContDiff ℝ ∞ c → ∀ (a b : ℝ), a ≤ b →
      (∀ t, ‖c t‖ = 1) → c a = p →
      c b = Real.cos r₀ • p + Real.sin r₀ • v₀ →
      r₀ ≤ arcLength (innerProductSpaceMetric E) c a b) ∧
    (∀ (U : Set (EuclideanSpace ℝ (Fin n))), IsOpen U → U.Nonempty →
      ∀ F : EuclideanSpace ℝ (Fin n) → sphere (0 : E) 1,
      (∀ x ∈ U, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ F x) →
      (∀ x ∈ U, Function.Injective
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) F x)) →
      (∀ x ∈ U, ∀ u v : EuclideanSpace ℝ (Fin n),
        ⟪u, v⟫_ℝ = (sphereMetricUnit (n := n) E).metricInner (F x)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) F x u)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) F x v)) →
      False) := by
  obtain ⟨h1, h2, _, h4, h5, _⟩ := exercise1_6_20_greatCircle hp hv hpv
  refine ⟨⟨h1, h2, h4, h5⟩, (exercise1_6_20_polar hp).2.1, ?_, ?_, ?_⟩
  · exact (exercise1_6_20_radialField hp hv hpv hr).2
  · intro c hc a b hab hsphere hca hcb
    exact (exercise1_6_20_minimize hp hv hpv hr hc hab hsphere hca hcb).1
  · intro U hU hne F hFd hFinj hFiso
    exact exercise1_6_20_no_immersion hn hU hne F hFd hFinj hFiso

end Exercise20

/-! ## Exercise 1.6.21 — hyperbolas minimize on hyperbolic space

The minimization argument mirrors Exercise 1.6.20 with the Minkowski form
`η` in place of the Euclidean inner product: the section below develops the
linear-algebraic facts about `η` on the upper hyperboloid sheet — positive
(semi)definiteness on tangent hyperplanes, Cauchy–Schwarz there, the reverse
Cauchy–Schwarz inequality `−η(x,y) ≥ 1` for sheet points — stated over an
arbitrary real inner-product spatial factor `F`. -/

section MinkowskiTangent

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "η" => minkowskiForm F ℝ

/-- **Eng.** The Minkowski form is **positive semidefinite on the tangent
hyperplane of the hyperboloid**: for `m` with `η(m,m) = −1`, `m_t > 0` and `z`
with `η(m,z) = 0`, Cauchy–Schwarz on the spatial parts gives `η(z,z) ≥ 0`. -/
theorem minkowskiForm_tangent_nonneg {m z : F × ℝ}
    (hm : η m m = -1) (hm2 : 0 < m.2) (hz : η m z = 0) :
    0 ≤ η z z := by
  have hinner : ∀ x y : ℝ, ⟪x, y⟫_ℝ = y * x := fun _ _ => rfl
  have hm' : ⟪m.1, m.1⟫_ℝ = m.2 ^ 2 - 1 := by
    have h := hm
    simp only [minkowskiForm_apply, hinner] at h
    nlinarith [h]
  have hz' : ⟪m.1, z.1⟫_ℝ = m.2 * z.2 := by
    have h := hz
    simp only [minkowskiForm_apply, hinner] at h
    linarith [h]
  have hCS := real_inner_mul_inner_self_le m.1 z.1
  rw [hz', hm'] at hCS
  have hz1 : (0 : ℝ) ≤ ⟪z.1, z.1⟫_ℝ := real_inner_self_nonneg
  simp only [minkowskiForm_apply, hinner]
  nlinarith [hCS, hz1, sq_nonneg z.2, mul_pos hm2 hm2]

/-- **Eng.** The Minkowski form is **positive definite on the tangent
hyperplane**: a null tangent vector at a hyperboloid point vanishes. -/
theorem minkowskiForm_tangent_eq_zero {m z : F × ℝ}
    (hm : η m m = -1) (hm2 : 0 < m.2) (hz : η m z = 0) (hzz : η z z = 0) :
    z = 0 := by
  have hinner : ∀ x y : ℝ, ⟪x, y⟫_ℝ = y * x := fun _ _ => rfl
  have hm' : ⟪m.1, m.1⟫_ℝ = m.2 ^ 2 - 1 := by
    have h := hm
    simp only [minkowskiForm_apply, hinner] at h
    nlinarith [h]
  have hz' : ⟪m.1, z.1⟫_ℝ = m.2 * z.2 := by
    have h := hz
    simp only [minkowskiForm_apply, hinner] at h
    linarith [h]
  have hzz' : ⟪z.1, z.1⟫_ℝ = z.2 ^ 2 := by
    have h := hzz
    simp only [minkowskiForm_apply, hinner] at h
    nlinarith [h]
  have hCS := real_inner_mul_inner_self_le m.1 z.1
  rw [hz', hm', hzz'] at hCS
  have hz2 : z.2 = 0 := by nlinarith [hCS, sq_nonneg z.2, mul_pos hm2 hm2]
  have hz1 : z.1 = 0 := by
    have h0 : ⟪z.1, z.1⟫_ℝ = 0 := by rw [hzz', hz2]; ring
    exact inner_self_eq_zero.mp h0
  exact Prod.ext hz1 hz2

/-- **Eng.** **Cauchy–Schwarz on the tangent hyperplane** of the hyperboloid:
for tangent vectors `v, w` at `m` (i.e. `η(m,v) = η(m,w) = 0`),
`η(v,w)² ≤ η(v,v) η(w,w)` — the discriminant argument for the positive
semidefinite restriction of `η`. -/
theorem minkowskiForm_tangent_inner_mul_le {m v w : F × ℝ}
    (hm : η m m = -1) (hm2 : 0 < m.2) (hv : η m v = 0) (hw : η m w = 0) :
    η v w ^ 2 ≤ η v v * η w w := by
  have hexpand : ∀ (s : ℝ) (x y : F × ℝ), η (x + s • y) (x + s • y)
      = η x x + 2 * s * η x y + s ^ 2 * η y y := by
    intro s x y
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    rw [minkowskiForm_comm F ℝ y x]
    ring
  have htangent : ∀ s : ℝ, η m (v + s • w) = 0 := by
    intro s
    rw [map_add, map_smul, hv, hw]
    simp
  have hpsd : ∀ s : ℝ, 0 ≤ η v v + 2 * s * η v w + s ^ 2 * η w w := by
    intro s
    have h := minkowskiForm_tangent_nonneg hm hm2 (htangent s)
    rw [hexpand s v w] at h
    exact h
  rcases eq_or_lt_of_le (minkowskiForm_tangent_nonneg hm hm2 hw) with hww | hww
  · -- `η(w,w) = 0`: the affine function `s ↦ η(v,v) + 2s η(v,w)` is bounded
    -- below, so `η(v,w) = 0`
    have hvw0 : η v w = 0 := by
      by_contra hne
      have h := hpsd (-(η v v + 1) / (2 * η v w))
      rw [← hww] at h
      have hval : 2 * (-(η v v + 1) / (2 * η v w)) * η v w
          = -(η v v + 1) := by
        field_simp
      nlinarith [h, hval]
    rw [hvw0, ← hww]
    simp
  · -- `η(w,w) > 0`: evaluate at the critical `s = −η(v,w)/η(w,w)`
    have h := hpsd (-(η v w) / η w w)
    have hcalc : η v v + 2 * (-(η v w) / η w w) * η v w
        + (-(η v w) / η w w) ^ 2 * η w w
        = η v v - η v w ^ 2 / η w w := by
      field_simp
      ring
    rw [hcalc] at h
    have hdiv : η v w ^ 2 / η w w ≤ η v v := by linarith [h]
    have := (div_le_iff₀ hww).mp hdiv
    linarith [this]

/-- **Eng.** **Reverse Cauchy–Schwarz** for the upper hyperboloid sheet: two
points `x, y` with `η(x,x) = η(y,y) = −1` and positive time coordinates
satisfy `−η(x,y) ≥ 1`. -/
theorem one_le_neg_minkowskiForm_of_sheet {x y : F × ℝ}
    (hx : η x x = -1) (hxpos : 0 < x.2) (hy : η y y = -1) (hypos : 0 < y.2) :
    1 ≤ -(η x y) := by
  have hinner : ∀ a b : ℝ, ⟪a, b⟫_ℝ = b * a := fun _ _ => rfl
  have hx' : ⟪x.1, x.1⟫_ℝ = x.2 ^ 2 - 1 := by
    have h := hx
    simp only [minkowskiForm_apply, hinner] at h
    nlinarith [h]
  have hy' : ⟪y.1, y.1⟫_ℝ = y.2 ^ 2 - 1 := by
    have h := hy
    simp only [minkowskiForm_apply, hinner] at h
    nlinarith [h]
  have hnx : ‖x.1‖ ^ 2 = x.2 ^ 2 - 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hx'
  have hny : ‖y.1‖ ^ 2 = y.2 ^ 2 - 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hy'
  have hx2 : 1 ≤ x.2 := by nlinarith [sq_nonneg ‖x.1‖, hnx, hxpos]
  have hy2 : 1 ≤ y.2 := by nlinarith [sq_nonneg ‖y.1‖, hny, hypos]
  have hCS : ⟪x.1, y.1⟫_ℝ ≤ ‖x.1‖ * ‖y.1‖ := real_inner_le_norm x.1 y.1
  have hprod : ‖x.1‖ * ‖y.1‖ + 1 ≤ x.2 * y.2 := by
    have hsq : (‖x.1‖ * ‖y.1‖ + 1) ^ 2 ≤ (x.2 * y.2) ^ 2 := by
      nlinarith [sq_nonneg (‖x.1‖ - ‖y.1‖), hnx, hny,
        mul_nonneg (norm_nonneg x.1) (norm_nonneg y.1)]
    nlinarith [hsq, mul_nonneg (norm_nonneg x.1) (norm_nonneg y.1),
      mul_pos (lt_of_lt_of_le zero_lt_one hx2)
        (lt_of_lt_of_le zero_lt_one hy2)]
  simp only [minkowskiForm_apply, hinner]
  nlinarith [hCS, hprod]

/-- **Eng.** A differentiable curve on the hyperboloid (`η(c,c) ≡ −1`) has
velocity tangent to it: `η(c, ċ) = 0`. -/
theorem minkowskiForm_inner_deriv_eq_zero {c : ℝ → F × ℝ}
    (hc : Differentiable ℝ c) (hH : ∀ t, η (c t) (c t) = -1) (t : ℝ) :
    η (c t) (deriv c t) = 0 := by
  -- coordinatewise: `η(c, c) = ⟪c₁, c₁⟫ − c₂ c₂` is constant
  have hc1 : HasDerivAt (fun s => (c s).1) (deriv c t).1 t := by
    simpa using ((ContinuousLinearMap.fst ℝ F ℝ).hasFDerivAt
      (x := c t)).comp_hasDerivAt t (hc t).hasDerivAt
  have hc2 : HasDerivAt (fun s => (c s).2) (deriv c t).2 t := by
    simpa using ((ContinuousLinearMap.snd ℝ F ℝ).hasFDerivAt
      (x := c t)).comp_hasDerivAt t (hc t).hasDerivAt
  have hd : HasDerivAt
      (fun s => ⟪(c s).1, (c s).1⟫_ℝ - (c s).2 * (c s).2)
      ((⟪(c t).1, (deriv c t).1⟫_ℝ + ⟪(deriv c t).1, (c t).1⟫_ℝ)
        - ((deriv c t).2 * (c t).2 + (c t).2 * (deriv c t).2)) t :=
    (HasDerivAt.inner ℝ hc1 hc1).sub (hc2.mul hc2)
  have hconst : (fun s => ⟪(c s).1, (c s).1⟫_ℝ - (c s).2 * (c s).2)
      = fun _ => (-1 : ℝ) := by
    funext s
    have h := hH s
    simp only [minkowskiForm_apply] at h
    exact h
  have h0 : deriv (fun s => ⟪(c s).1, (c s).1⟫_ℝ - (c s).2 * (c s).2) t
      = 0 := by
    rw [hconst]
    exact deriv_const t (-1)
  have hzero := hd.deriv
  rw [h0] at hzero
  have hcomm : ⟪(deriv c t).1, (c t).1⟫_ℝ = ⟪(c t).1, (deriv c t).1⟫_ℝ :=
    real_inner_comm _ _
  have hmul : (deriv c t).2 * (c t).2 = (c t).2 * (deriv c t).2 :=
    mul_comm _ _
  simp only [minkowskiForm_apply]
  have hinner : ⟪(c t).2, (deriv c t).2⟫_ℝ = (deriv c t).2 * (c t).2 :=
    rfl
  rw [hinner]
  linarith [hzero, hcomm, hmul]

/-- **Math.** **Hyperbolic distance bounds Minkowski arc length from below**:
for a smooth curve `c` on the upper hyperboloid sheet (`η(c,c) = −1`,
`c_t > 0`), `arcosh(−η(c a, c b)) ≤ ∫ √η(ċ, ċ)` — the mirror of
`arccos_inner_le_arcLength`, with the mollified radial coordinate
`f_ε(t) = arcosh(−η(c a, c t) + ε)` (differentiable since `arcosh` is
differentiable on `(1, ∞)` and `−η(c a, c t) ≥ 1` by the reverse
Cauchy–Schwarz inequality `one_le_neg_minkowskiForm_of_sheet`), whose
derivative is bounded by the hyperbolic speed via Cauchy–Schwarz on the
tangent hyperplane. -/
theorem arcosh_neg_minkowskiForm_le_length {c : ℝ → F × ℝ}
    (hc : ContDiff ℝ ∞ c) {a b : ℝ} (hab : a ≤ b)
    (hH : ∀ t, η (c t) (c t) = -1 ∧ 0 < (c t).2) :
    Real.arcosh (-(η (c a) (c b)))
      ≤ ∫ t in a..b, Real.sqrt (η (deriv c t) (deriv c t)) := by
  have hcd : Differentiable ℝ c := hc.differentiable (by simp)
  have hderiv_cont : Continuous (deriv c) := hc.continuous_deriv (by simp)
  have horth : ∀ t, η (c t) (deriv c t) = 0 :=
    minkowskiForm_inner_deriv_eq_zero hcd fun t => (hH t).1
  -- the radial height `u t = −η(c a, c t)` and its properties
  set u : ℝ → ℝ := fun t => -(η (c a) (c t)) with hu_def
  have hu_deriv : ∀ t, HasDerivAt u (-(η (c a) (deriv c t))) t := by
    intro t
    have h1 : HasDerivAt (fun s => η (c a) (c s)) (η (c a) (deriv c t)) t :=
      ((minkowskiForm F ℝ (c a)).hasFDerivAt (x := c t)).comp_hasDerivAt t
        (hcd t).hasDerivAt
    simpa using h1.neg
  have hu_cont : Continuous u :=
    ((minkowskiForm F ℝ (c a)).continuous.comp hc.continuous).neg
  have hu'_cont : Continuous fun t => -(η (c a) (deriv c t)) :=
    ((minkowskiForm F ℝ (c a)).continuous.comp hderiv_cont).neg
  have hspeed_sq_nonneg : ∀ t, 0 ≤ η (deriv c t) (deriv c t) := fun t =>
    minkowskiForm_tangent_nonneg (hH t).1 (hH t).2 (horth t)
  have hspeed_cont :
      Continuous fun t => Real.sqrt (η (deriv c t) (deriv c t)) :=
    Real.continuous_sqrt.comp
      (((minkowskiForm F ℝ).continuous.comp hderiv_cont).clm_apply
        hderiv_cont)
  have hu_ge : ∀ t, 1 ≤ u t := fun t =>
    one_le_neg_minkowskiForm_of_sheet (hH a).1 (hH a).2 (hH t).1 (hH t).2
  -- the tangential Cauchy–Schwarz bound on `u'`
  have hu'_sq_bound : ∀ t, (η (c a) (deriv c t)) ^ 2
      ≤ (u t ^ 2 - 1) * η (deriv c t) (deriv c t) := by
    intro t
    have hm := (hH t).1
    have hm2 := (hH t).2
    have hpx' : η (c a) (c t) = -(u t) := by simp only [hu_def]; ring
    have hxp' : η (c t) (c a) = -(u t) := by
      rw [minkowskiForm_comm F ℝ (c t) (c a)]
      exact hpx'
    -- the part of `c a` tangential at `c t`
    have hpT_tangent : η (c t) (c a - u t • c t) = 0 := by
      rw [map_sub, map_smul]
      simp only [smul_eq_mul]
      rw [hxp', hm]
      ring
    have hpT_self : η (c a - u t • c t) (c a - u t • c t) = u t ^ 2 - 1 := by
      simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
      rw [hpx', hxp', (hH a).1, hm]
      ring
    have hpT_deriv : η (c a - u t • c t) (deriv c t)
        = η (c a) (deriv c t) := by
      simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
      rw [horth t]
      ring
    have hCS := minkowskiForm_tangent_inner_mul_le hm hm2 hpT_tangent (horth t)
    rw [hpT_deriv, hpT_self] at hCS
    exact hCS
  have hu'_bound : ∀ t, |(-(η (c a) (deriv c t)))|
      ≤ Real.sqrt (u t ^ 2 - 1)
        * Real.sqrt (η (deriv c t) (deriv c t)) := by
    intro t
    have hD_nonneg : (0 : ℝ) ≤ u t ^ 2 - 1 := by nlinarith [hu_ge t]
    rw [abs_neg, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hD_nonneg]
    exact Real.sqrt_le_sqrt (hu'_sq_bound t)
  -- the mollified estimate, for every `ε > 0`
  have key : ∀ ε : ℝ, 0 < ε →
      Real.arcosh (u b + ε) - Real.arcosh (u a + ε)
        ≤ ∫ t in a..b, Real.sqrt (η (deriv c t) (deriv c t)) := by
    intro ε hε
    set f' : ℝ → ℝ := fun t =>
      (Real.sqrt ((u t + ε) ^ 2 - 1))⁻¹ * (-(η (c a) (deriv c t)))
      with hf'_def
    have harg_gt : ∀ t, 1 < u t + ε := fun t => by linarith [hu_ge t]
    have hD_pos : ∀ t, 0 < (u t + ε) ^ 2 - 1 := by
      intro t
      nlinarith [harg_gt t]
    have hsqrt_pos : ∀ t, 0 < Real.sqrt ((u t + ε) ^ 2 - 1) :=
      fun t => Real.sqrt_pos.mpr (hD_pos t)
    have hf_deriv : ∀ t,
        HasDerivAt (fun s => Real.arcosh (u s + ε)) (f' t) t := by
      intro t
      have h1 : HasDerivAt (fun s => u s + ε) (-(η (c a) (deriv c t))) t :=
        (hu_deriv t).add_const ε
      have hcomp := HasDerivAt.comp t
        (Real.hasDerivAt_arcosh (mem_Ioi.mpr (harg_gt t))) h1
      simpa [Function.comp, hf'_def] using hcomp
    have hf'_bound : ∀ t,
        |f' t| ≤ Real.sqrt (η (deriv c t) (deriv c t)) := by
      intro t
      have habs : |f' t| = (Real.sqrt ((u t + ε) ^ 2 - 1))⁻¹
          * |(-(η (c a) (deriv c t)))| := by
        simp only [hf'_def]
        rw [abs_mul, abs_inv, abs_of_pos (hsqrt_pos t)]
      rw [habs, inv_mul_le_iff₀ (hsqrt_pos t)]
      calc |(-(η (c a) (deriv c t)))|
          ≤ Real.sqrt (u t ^ 2 - 1)
            * Real.sqrt (η (deriv c t) (deriv c t)) := hu'_bound t
        _ ≤ Real.sqrt ((u t + ε) ^ 2 - 1)
            * Real.sqrt (η (deriv c t) (deriv c t)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
            apply Real.sqrt_le_sqrt
            nlinarith [hu_ge t]
    have hf'_cont : Continuous f' := by
      apply Continuous.mul
      · apply Continuous.inv₀
        · exact Real.continuous_sqrt.comp
            (((hu_cont.add continuous_const).pow 2).sub continuous_const)
        · exact fun t => (hsqrt_pos t).ne'
      · exact hu'_cont
    have hFTC : ∫ t in a..b, f' t
        = Real.arcosh (u b + ε) - Real.arcosh (u a + ε) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hf_deriv t) (hf'_cont.intervalIntegrable a b)
    calc Real.arcosh (u b + ε) - Real.arcosh (u a + ε)
        = ∫ t in a..b, f' t := hFTC.symm
      _ ≤ |∫ t in a..b, f' t| := le_abs_self _
      _ ≤ ∫ t in a..b, |f' t| :=
          intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ t in a..b, Real.sqrt (η (deriv c t) (deriv c t)) :=
          intervalIntegral.integral_mono_on hab
            (hf'_cont.abs.intervalIntegrable a b)
            (hspeed_cont.intervalIntegrable a b)
            (fun t _ => hf'_bound t)
  -- pass to the limit `ε → 0⁺`
  have htends : ∀ t₀ : ℝ, 1 ≤ u t₀ →
      Filter.Tendsto (fun ε : ℝ => Real.arcosh (u t₀ + ε))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.arcosh (u t₀))) := by
    intro t₀ ht₀
    have harg : Filter.Tendsto (fun ε : ℝ => u t₀ + ε)
        (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin (u t₀) (Set.Ici 1)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have h1 : Filter.Tendsto (fun ε : ℝ => u t₀ + ε) (nhds 0)
            (nhds (u t₀ + 0)) := (continuous_const.add continuous_id).tendsto 0
        rw [add_zero] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      · exact Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => by
          have : (0 : ℝ) < ε := hε
          simp only [Set.mem_Ici]
          linarith
    exact (Real.continuousOn_arcosh (u t₀) (by simpa using ht₀)).tendsto.comp
      harg
  have hua : u a = 1 := by
    simp only [hu_def]
    rw [(hH a).1]
    norm_num
  have hlim : Filter.Tendsto (fun ε : ℝ =>
      Real.arcosh (u b + ε) - Real.arcosh (u a + ε))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.arcosh (u b) - Real.arcosh (u a))) :=
    (htends b (hu_ge b)).sub (htends a (hu_ge a))
  have hfinal : Real.arcosh (u b) - Real.arcosh (u a)
      ≤ ∫ t in a..b, Real.sqrt (η (deriv c t) (deriv c t)) :=
    le_of_tendsto hlim
      (Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => key ε hε)
  have hend : Real.arcosh (-(η (c a) (c b))) = Real.arcosh (u b) := by
    simp only [hu_def]
  rw [hend]
  rw [hua, Real.arcosh_zero, sub_zero] at hfinal
  exact hfinal

/-- **Eng.** The time coordinate of `cosh s • p + sinh s • v` is positive for
`p` on the upper sheet and `v` a unit tangent at `p` — the Cauchy–Schwarz
positivity computation of Exercise 1.6.21 (1), in general spatial factor. -/
theorem minkowski_hyperbola_time_pos {p v : F × ℝ}
    (hp : η p p = -1) (hppos : 0 < p.2) (hv : η v v = 1) (hpv : η p v = 0)
    (s : ℝ) : 0 < (Real.cosh s • p + Real.sinh s • v).2 := by
  have hinner : ∀ x y : ℝ, ⟪x, y⟫_ℝ = y * x := fun _ _ => rfl
  have hp1 : ⟪p.1, p.1⟫_ℝ = p.2 ^ 2 - 1 := by
    have h := hp
    simp only [minkowskiForm_apply, hinner] at h
    nlinarith [h]
  have hv1 : ⟪v.1, v.1⟫_ℝ = v.2 ^ 2 + 1 := by
    have h := hv
    simp only [minkowskiForm_apply, hinner] at h
    nlinarith [h]
  have hpv1 : ⟪p.1, v.1⟫_ℝ = p.2 * v.2 := by
    have h := hpv
    simp only [minkowskiForm_apply, hinner] at h
    linarith [h]
  have hCS := real_inner_mul_inner_self_le p.1 v.1
  rw [hp1, hv1, hpv1] at hCS
  have hb2 : v.2 ^ 2 ≤ p.2 ^ 2 - 1 := by nlinarith [hCS]
  have hpsq : 1 ≤ p.2 ^ 2 := by
    have h0 : (0 : ℝ) ≤ ⟪p.1, p.1⟫_ℝ := real_inner_self_nonneg
    rw [hp1] at h0
    linarith
  show 0 < Real.cosh s * p.2 + Real.sinh s * v.2
  nlinarith [Real.cosh_pos s, Real.cosh_sq_sub_sinh_sq s, hppos,
    mul_pos (Real.cosh_pos s) hppos, sq_nonneg p.2, hpsq,
    mul_le_mul_of_nonneg_left hb2 (sq_nonneg (Real.sinh s)),
    sq_nonneg (Real.cosh s * p.2 + Real.sinh s * v.2)]

/-- **Eng.** `cosh s • p + sinh s • v` stays on the hyperboloid for `p` on it
and `v` a unit tangent. -/
theorem minkowski_hyperbola_self {p v : F × ℝ}
    (hp : η p p = -1) (hv : η v v = 1) (hpv : η p v = 0) (s : ℝ) :
    η (Real.cosh s • p + Real.sinh s • v)
      (Real.cosh s • p + Real.sinh s • v) = -1 := by
  have hvp : η v p = 0 := by rw [minkowskiForm_comm]; exact hpv
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  rw [hp, hv, hpv, hvp]
  nlinarith [Real.cosh_sq_sub_sinh_sq s]

/-- **Eng.** Equality in the **hyperbolic triangle inequality**: a point `x`
on the upper sheet with `arcosh(−η(p,x)) + arcosh(−η(x,q)) ≤ r₀`, where
`q = cosh r₀ • p + sinh r₀ • v₀` (`p` on the sheet, `v₀` a unit tangent,
`r₀ > 0`), lies on the hyperbola from `p` through `q`:
`x = cosh s • p + sinh s • v₀` with `s = arcosh(−η(p,x)) ∈ [0, r₀]`. -/
theorem eq_hyperbola_of_arcosh_add_arcosh_le {p v₀ x : F × ℝ}
    (hp : η p p = -1) (hppos : 0 < p.2) (hv : η v₀ v₀ = 1) (hpv : η p v₀ = 0)
    {r₀ : ℝ} (hr : 0 < r₀) (hx : η x x = -1) (hxpos : 0 < x.2)
    (hsum : Real.arcosh (-(η p x))
      + Real.arcosh (-(η x (Real.cosh r₀ • p + Real.sinh r₀ • v₀))) ≤ r₀) :
    Real.arcosh (-(η p x)) ∈ Icc 0 r₀ ∧
    x = Real.cosh (Real.arcosh (-(η p x))) • p
        + Real.sinh (Real.arcosh (-(η p x))) • v₀ := by
  set q : F × ℝ := Real.cosh r₀ • p + Real.sinh r₀ • v₀ with hq_def
  have hq_sheet : η q q = -1 := by
    rw [hq_def]
    exact minkowski_hyperbola_self hp hv hpv r₀
  have hq_pos : 0 < q.2 := by
    rw [hq_def]
    exact minkowski_hyperbola_time_pos hp hppos hv hpv r₀
  set ux : ℝ := -(η p x) with hux_def
  have hux_ge : 1 ≤ ux :=
    one_le_neg_minkowskiForm_of_sheet hp hppos hx hxpos
  set α : ℝ := Real.arcosh ux with hα_def
  set β : ℝ := Real.arcosh (-(η x q)) with hβ_def
  have hxq_ge : 1 ≤ -(η x q) :=
    one_le_neg_minkowskiForm_of_sheet hx hxpos hq_sheet hq_pos
  have hα_nonneg : 0 ≤ α := Real.arcosh_nonneg hux_ge
  have hβ_nonneg : 0 ≤ β := Real.arcosh_nonneg hxq_ge
  have hα_le : α ≤ r₀ := by linarith [hβ_nonneg, hsum]
  refine ⟨⟨hα_nonneg, hα_le⟩, ?_⟩
  have hcoshα : Real.cosh α = ux := Real.cosh_arcosh hux_ge
  have hsinhα : Real.sinh α = Real.sqrt (ux ^ 2 - 1) :=
    Real.sinh_arcosh hux_ge
  have hsinhα_nonneg : 0 ≤ Real.sinh α := by
    rw [hsinhα]; exact Real.sqrt_nonneg _
  have hpx' : η p x = -ux := by rw [hux_def]; ring
  have hxp' : η x p = -ux := by
    rw [minkowskiForm_comm F ℝ x p]
    exact hpx'
  rcases eq_or_lt_of_le hsinhα_nonneg with hsinh0 | hsinh_pos
  · -- `sinh α = 0` forces `−η(p,x) = 1`, hence `x = p` by definiteness
    have hux1 : ux = 1 := by
      have h1 : Real.sqrt (ux ^ 2 - 1) = 0 := by
        rw [← hsinhα]; exact hsinh0.symm
      have h2 : ux ^ 2 - 1 ≤ 0 := by
        by_contra hgt
        push_neg at hgt
        exact absurd h1 (Real.sqrt_pos.mpr hgt).ne'
      nlinarith [hux_ge]
    have hα0 : α = 0 := by
      rw [hα_def, hux1]
      exact Real.arcosh_zero
    have hxp : x = p := by
      have htang : η p (x - p) = 0 := by
        rw [map_sub, hpx', hp, hux1]
        ring
      have hnull : η (x - p) (x - p) = 0 := by
        simp only [map_sub, ContinuousLinearMap.sub_apply]
        rw [hpx', hxp', hx, hp, hux1]
        ring
      have hz := minkowskiForm_tangent_eq_zero hp hppos htang hnull
      rw [sub_eq_zero.mp hz]
    rw [hα0, hxp]
    simp
  · -- main case: `sinh α > 0`, decompose `x = cosh α • p + sinh α • w`
    have hsinhr₀_pos : 0 < Real.sinh r₀ := Real.sinh_pos_iff.mpr hr
    have hD_pos : 0 < ux ^ 2 - 1 := by
      have h := hsinh_pos
      rw [hsinhα] at h
      exact Real.sqrt_pos.mp h
    have hxT_tangent : η p (x - ux • p) = 0 := by
      rw [map_sub, map_smul]
      simp only [smul_eq_mul]
      rw [hpx', hp]
      ring
    have hxT_self : η (x - ux • p) (x - ux • p) = ux ^ 2 - 1 := by
      simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
      rw [hpx', hxp', hx, hp]
      ring
    set w : F × ℝ := (Real.sinh α)⁻¹ • (x - ux • p) with hw_def
    have hw_tangent : η p w = 0 := by
      rw [hw_def, map_smul]
      simp only [smul_eq_mul]
      rw [hxT_tangent]
      ring
    have hw_self : η w w = 1 := by
      rw [hw_def]
      simp only [map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply,
        smul_eq_mul]
      rw [hxT_self, hsinhα, ← mul_assoc, ← mul_inv,
        Real.mul_self_sqrt hD_pos.le, inv_mul_cancel₀ hD_pos.ne']
    have hx_decomp : x = Real.cosh α • p + Real.sinh α • w := by
      rw [hw_def, smul_smul, mul_inv_cancel₀ hsinh_pos.ne', one_smul, hcoshα]
      abel
    have hwp : η w p = 0 := by
      rw [minkowskiForm_comm F ℝ w p]
      exact hw_tangent
    have hxq_eq : -(η x q) = Real.cosh α * Real.cosh r₀
        - Real.sinh α * Real.sinh r₀ * η w v₀ := by
      rw [hx_decomp, hq_def]
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
      rw [hp, hpv, hwp]
      ring
    have hwv_le : η w v₀ ≤ 1 := by
      have hCS := minkowskiForm_tangent_inner_mul_le hp hppos hw_tangent hpv
      rw [hw_self, hv] at hCS
      nlinarith [hCS]
    have hcoshβ : Real.cosh β = -(η x q) := Real.cosh_arcosh hxq_ge
    have hβ_le : β ≤ r₀ - α := by linarith [hsum]
    have hcosh_mono : Real.cosh β ≤ Real.cosh (r₀ - α) := by
      rw [Real.cosh_le_cosh, abs_of_nonneg hβ_nonneg,
        abs_of_nonneg (by linarith [hα_le] : (0 : ℝ) ≤ r₀ - α)]
      exact hβ_le
    have hcosh_sub : Real.cosh (r₀ - α)
        = Real.cosh r₀ * Real.cosh α - Real.sinh r₀ * Real.sinh α :=
      Real.cosh_sub r₀ α
    have hwv_ge : 1 ≤ η w v₀ := by
      rw [hcoshβ, hxq_eq, hcosh_sub] at hcosh_mono
      have hprod_pos : 0 < Real.sinh α * Real.sinh r₀ :=
        mul_pos hsinh_pos hsinhr₀_pos
      nlinarith [hcosh_mono, hprod_pos]
    have hwv : η w v₀ = 1 := le_antisymm hwv_le hwv_ge
    have hw_eq : w = v₀ := by
      have hvw : η v₀ w = 1 := by
        rw [minkowskiForm_comm F ℝ v₀ w]
        exact hwv
      have htang : η p (w - v₀) = 0 := by
        rw [map_sub, hw_tangent, hpv]
        ring
      have hnull : η (w - v₀) (w - v₀) = 0 := by
        simp only [map_sub, ContinuousLinearMap.sub_apply]
        rw [hw_self, hv, hwv, hvw]
        ring
      have hz := minkowskiForm_tangent_eq_zero hp hppos htang hnull
      rw [sub_eq_zero.mp hz]
    rw [hx_decomp, hw_eq]

end MinkowskiTangent

section Exercise21

variable {n : ℕ}

/-- Abbreviation for the ambient Minkowski space `ℝ^{n,1}` of Exercise
1.6.21. -/
local notation "𝕄" => (EuclideanSpace ℝ (Fin n) × ℝ)

/-- Abbreviation for the Minkowski form on `ℝ^{n,1}`. -/
local notation "η" => minkowskiForm (EuclideanSpace ℝ (Fin n)) ℝ

/-- **Math.** Exercise 1.6.21 (1): for `p` on the hyperboloid
(`η(p,p) = −1`, `p_t > 0`) and a unit tangent `v` (`η(v,v) = 1`,
`η(p,v) = 0`), the **hyperbola** `c(t) = p cosh t + v sinh t` stays on `Hⁿ`,
starts at `p` with velocity `v`, and has unit speed `η(ċ, ċ) = 1` (the speed
in the induced metric of `hyperbolicSpace`, cf.
`hyperbolicSpace_metricInner`). -/
theorem exercise1_6_21_hyperbola {p v : 𝕄}
    (hp : η p p = -1) (hppos : 0 < p.2) (hv : η v v = 1) (hpv : η p v = 0) :
    (∀ t, η (Real.cosh t • p + Real.sinh t • v)
      (Real.cosh t • p + Real.sinh t • v) = -1) ∧
    (∀ t, 0 < (Real.cosh t • p + Real.sinh t • v).2) ∧
    Real.cosh 0 • p + Real.sinh 0 • v = p ∧
    (∀ t, HasDerivAt (fun s => Real.cosh s • p + Real.sinh s • v)
      (Real.sinh t • p + Real.cosh t • v) t) ∧
    deriv (fun s => Real.cosh s • p + Real.sinh s • v) 0 = v ∧
    (∀ t, η (deriv (fun s => Real.cosh s • p + Real.sinh s • v) t)
      (deriv (fun s => Real.cosh s • p + Real.sinh s • v) t) = 1) := by
  have hvp : η v p = 0 := by rw [minkowskiForm_comm]; exact hpv
  have hexpand : ∀ s t : ℝ, η (s • p + t • v) (s • p + t • v)
      = s ^ 2 * η p p + t ^ 2 * η v v + 2 * (s * t) * η p v := by
    intro s t
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    rw [minkowskiForm_comm _ _ v p]
    ring
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s => Real.cosh s • p + Real.sinh s • v)
      (Real.sinh t • p + Real.cosh t • v) t := fun t =>
    ((Real.hasDerivAt_cosh t).smul_const p).add
      ((Real.hasDerivAt_sinh t).smul_const v)
  refine ⟨fun t => ?_, fun t => ?_, by simp, hderiv, ?_, fun t => ?_⟩
  · rw [hexpand, hp, hv, hpv]
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  · -- positivity of the time coordinate: Cauchy–Schwarz on the spatial parts
    -- gives `v.2² ≤ p.2² − 1 < p.2²`, and `|sinh| < cosh` does the rest
    have hinner : ∀ x y : ℝ, ⟪x, y⟫_ℝ = y * x := fun _ _ => rfl
    have hp1 : ⟪p.1, p.1⟫_ℝ = p.2 ^ 2 - 1 := by
      have h := hp
      simp only [minkowskiForm_apply, hinner] at h
      nlinarith [h]
    have hv1 : ⟪v.1, v.1⟫_ℝ = v.2 ^ 2 + 1 := by
      have h := hv
      simp only [minkowskiForm_apply, hinner] at h
      nlinarith [h]
    have hpv1 : ⟪p.1, v.1⟫_ℝ = p.2 * v.2 := by
      have h := hpv
      simp only [minkowskiForm_apply, hinner] at h
      linarith [h]
    have hCS := real_inner_mul_inner_self_le p.1 v.1
    rw [hp1, hv1, hpv1] at hCS
    have hb2 : v.2 ^ 2 ≤ p.2 ^ 2 - 1 := by nlinarith [hCS]
    have hpsq : 1 ≤ p.2 ^ 2 := by
      have h0 : (0 : ℝ) ≤ ⟪p.1, p.1⟫_ℝ := real_inner_self_nonneg
      rw [hp1] at h0
      linarith
    show 0 < Real.cosh t * p.2 + Real.sinh t * v.2
    nlinarith [Real.cosh_pos t, Real.cosh_sq_sub_sinh_sq t, hppos,
      mul_pos (Real.cosh_pos t) hppos, sq_nonneg p.2, hpsq,
      mul_le_mul_of_nonneg_left hb2 (sq_nonneg (Real.sinh t)),
      sq_nonneg (Real.cosh t * p.2 + Real.sinh t * v.2)]
  · rw [(hderiv 0).deriv]
    simp
  · rw [(hderiv t).deriv, hexpand, hp, hv, hpv]
    nlinarith [Real.cosh_sq_sub_sinh_sq t]

/-- **Math.** Exercise 1.6.21 (3): the radial field on `Hⁿ − {p}`. At
`q = p cosh r₀ + v₀ sinh r₀` (`r₀ > 0`, `v₀` a unit tangent at `p`),
`∂_r|_q = ∂F/∂r(r₀, v₀) = p sinh r₀ + v₀ cosh r₀`, which agrees with the
announced intrinsic formula `(−p − (q ⋅ p)q)/√(−1 + (q ⋅ p)²)`. -/
theorem exercise1_6_21_radialField {p v₀ : 𝕄}
    (hp : η p p = -1) (hv : η v₀ v₀ = 1) (hpv : η p v₀ = 0)
    {r₀ : ℝ} (hr : 0 < r₀) :
    deriv (fun r => Real.cosh r • p + Real.sinh r • v₀) r₀
      = Real.sinh r₀ • p + Real.cosh r₀ • v₀ ∧
    (Real.sqrt (-1 + (η (Real.cosh r₀ • p + Real.sinh r₀ • v₀) p) ^ 2))⁻¹ •
        (-p - (η (Real.cosh r₀ • p + Real.sinh r₀ • v₀) p) •
          (Real.cosh r₀ • p + Real.sinh r₀ • v₀))
      = Real.sinh r₀ • p + Real.cosh r₀ • v₀ := by
  have hvp : η v₀ p = 0 := by rw [minkowskiForm_comm]; exact hpv
  have hq : η (Real.cosh r₀ • p + Real.sinh r₀ • v₀) p = -Real.cosh r₀ := by
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    rw [hp, hvp]
    ring
  have hsinh_pos : 0 < Real.sinh r₀ := Real.sinh_pos_iff.mpr hr
  constructor
  · exact (((Real.hasDerivAt_cosh r₀).smul_const p).add
      ((Real.hasDerivAt_sinh r₀).smul_const v₀)).deriv
  · rw [hq]
    have hsqrt : Real.sqrt (-1 + (-Real.cosh r₀) ^ 2) = Real.sinh r₀ := by
      have h1 : (-1 : ℝ) + (-Real.cosh r₀) ^ 2 = Real.sinh r₀ ^ 2 := by
        rw [neg_sq, Real.cosh_sq]
        ring
      rw [h1]
      exact Real.sqrt_sq hsinh_pos.le
    rw [hsqrt]
    have hs0 : Real.sinh r₀ ≠ 0 := hsinh_pos.ne'
    match_scalars
    · field_simp
      nlinarith [Real.cosh_sq r₀]
    · field_simp

/-- **Math.** Exercise 1.6.21 (2): `F(r, w) = p cosh r + w sinh r` is smooth,
restricts to a bijection
`(0, ∞) × S^{n-1} → Hⁿ − {p}` (with `S^{n-1} = {w | η(p,w) = 0, η(w,w) = 1}`
the unit tangent sphere at `p`), and has a smooth inverse on the open set
`{x | 1 < −η(p, x)}` ⊇ `Hⁿ − {p}` — the diffeomorphism content of the
exercise, expressed ambiently. -/
theorem exercise1_6_21_polar {p : 𝕄} (hp : η p p = -1) (hppos : 0 < p.2) :
    ContDiff ℝ ∞ (fun q : ℝ × 𝕄 => Real.cosh q.1 • p + Real.sinh q.1 • q.2) ∧
    Set.BijOn (fun q : ℝ × 𝕄 => Real.cosh q.1 • p + Real.sinh q.1 • q.2)
      (Ioi 0 ×ˢ {w : 𝕄 | η p w = 0 ∧ η w w = 1})
      {x : 𝕄 | η x x = -1 ∧ 0 < x.2 ∧ x ≠ p} ∧
    ∃ Finv : 𝕄 → ℝ × 𝕄,
      ContDiffOn ℝ ∞ Finv {x : 𝕄 | 1 < -(η p x)} ∧
      ∀ q ∈ Ioi (0 : ℝ) ×ˢ {w : 𝕄 | η p w = 0 ∧ η w w = 1},
        Finv (Real.cosh q.1 • p + Real.sinh q.1 • q.2) = q := by
  -- the radial height of the image
  have hηpx : ∀ (r : ℝ) (w : 𝕄), η p w = 0 →
      η p (Real.cosh r • p + Real.sinh r • w) = -Real.cosh r := by
    intro r w hw
    rw [map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    rw [hp, hw]
    ring
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- smoothness of `F`
    exact ((Real.contDiff_cosh.comp contDiff_fst).smul contDiff_const).add
      ((Real.contDiff_sinh.comp contDiff_fst).smul contDiff_snd)
  · -- MapsTo
    rintro ⟨r, w⟩ ⟨hr, hw, hwn⟩
    have hr' : (0 : ℝ) < r := hr
    refine ⟨minkowski_hyperbola_self hp hwn hw r,
      minkowski_hyperbola_time_pos hp hppos hwn hw r, ?_⟩
    intro hxp
    have hxp' : Real.cosh r • p + Real.sinh r • w = p := hxp
    have h1 := hηpx r w hw
    rw [hxp', hp] at h1
    have hcosh1 : Real.cosh r = 1 := by linarith [h1]
    have := Real.one_lt_cosh.mpr hr'.ne'
    linarith
  · -- InjOn
    rintro ⟨r, w⟩ ⟨hr, hw, hwn⟩ ⟨r', w'⟩ ⟨hr', hw', hwn'⟩ heq
    have hr0 : (0 : ℝ) < r := hr
    have hr0' : (0 : ℝ) < r' := hr'
    have heq' : Real.cosh r • p + Real.sinh r • w
        = Real.cosh r' • p + Real.sinh r' • w' := heq
    have hcosh : Real.cosh r = Real.cosh r' := by
      have h1 := hηpx r w hw
      have h2 := hηpx r' w' hw'
      rw [heq'] at h1
      rw [h1] at h2
      linarith [h2]
    have hrr : r = r' :=
      Real.cosh_injOn (mem_Ici.mpr hr0.le) (mem_Ici.mpr hr0'.le) hcosh
    have hsinh_ne : Real.sinh r ≠ 0 := (Real.sinh_pos_iff.mpr hr0).ne'
    have hw_eq : w = w' := by
      have h3 : Real.sinh r • w = Real.sinh r • w' := by
        have h5 := heq'
        rw [← hrr] at h5
        have h4 := congrArg (fun x => x - Real.cosh r • p) h5
        simpa using h4
      have h6 : Real.sinh r • (w - w') = 0 := by
        rw [smul_sub, h3, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h6).resolve_left hsinh_ne)
    rw [Prod.ext_iff]
    exact ⟨hrr, hw_eq⟩
  · -- SurjOn
    rintro x ⟨hx_sheet, hx_pos, hx_ne⟩
    set u : ℝ := -(η p x) with hu_def
    have hu_ge : 1 ≤ u :=
      one_le_neg_minkowskiForm_of_sheet hp hppos hx_sheet hx_pos
    have hpx' : η p x = -u := by rw [hu_def]; ring
    have hxp' : η x p = -u := by
      rw [minkowskiForm_comm _ _ x p]
      exact hpx'
    have hu_gt : 1 < u := by
      rcases eq_or_lt_of_le hu_ge with h1 | h1
      · exfalso
        apply hx_ne
        have htang : η p (x - p) = 0 := by
          rw [map_sub, hpx', hp, ← h1]
          ring
        have hnull : η (x - p) (x - p) = 0 := by
          simp only [map_sub, ContinuousLinearMap.sub_apply]
          rw [hpx', hxp', hx_sheet, hp, ← h1]
          ring
        have hz := minkowskiForm_tangent_eq_zero hp hppos htang hnull
        exact sub_eq_zero.mp hz
      · exact h1
    set r : ℝ := Real.arcosh u with hr_def
    have hr_pos : 0 < r := Real.arcosh_pos hu_gt
    have hcosh_r : Real.cosh r = u := Real.cosh_arcosh hu_ge
    have hsinh_r : Real.sinh r = Real.sqrt (u ^ 2 - 1) :=
      Real.sinh_arcosh hu_ge
    have hsinh_pos : 0 < Real.sinh r := Real.sinh_pos_iff.mpr hr_pos
    have hD_pos : 0 < u ^ 2 - 1 := by nlinarith [hu_gt]
    have hxT_tangent : η p (x - u • p) = 0 := by
      rw [map_sub, map_smul]
      simp only [smul_eq_mul]
      rw [hpx', hp]
      ring
    have hxT_self : η (x - u • p) (x - u • p) = u ^ 2 - 1 := by
      simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
      rw [hpx', hxp', hx_sheet, hp]
      ring
    set w : 𝕄 := (Real.sinh r)⁻¹ • (x - u • p) with hw_def
    have hw_tangent : η p w = 0 := by
      rw [hw_def, map_smul]
      simp only [smul_eq_mul]
      rw [hxT_tangent]
      ring
    have hw_self : η w w = 1 := by
      rw [hw_def]
      simp only [map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply,
        smul_eq_mul]
      rw [hxT_self, hsinh_r, ← mul_assoc, ← mul_inv,
        Real.mul_self_sqrt hD_pos.le, inv_mul_cancel₀ hD_pos.ne']
    refine ⟨(r, w), ⟨hr_pos, hw_tangent, hw_self⟩, ?_⟩
    show Real.cosh r • p + Real.sinh r • w = x
    rw [hw_def, smul_smul, mul_inv_cancel₀ hsinh_pos.ne', one_smul, hcosh_r]
    abel
  · -- the smooth inverse
    refine ⟨fun x => (Real.arcosh (-(η p x)),
      (Real.sinh (Real.arcosh (-(η p x))))⁻¹ • (x - (-(η p x)) • p)),
      ?_, ?_⟩
    · -- smoothness on the open set `{x | 1 < −η(p,x)}`
      intro x hx
      have hx' : 1 < -(η p x) := hx
      have hu_cd : ContDiffAt ℝ ∞ (fun y : 𝕄 => -(η p y)) x :=
        ((minkowskiForm (EuclideanSpace ℝ (Fin n)) ℝ
          p).contDiff.neg).contDiffAt
      have harcosh : ContDiffAt ℝ ∞
          (fun y : 𝕄 => Real.arcosh (-(η p y))) x := by
        have hcomp := ContDiffAt.comp x
          (Real.contDiffAt_arcosh (mem_Ioi.mpr hx')) hu_cd
        simpa [Function.comp] using hcomp
      have hsinh_ne : Real.sinh (Real.arcosh (-(η p x))) ≠ 0 :=
        (Real.sinh_pos_iff.mpr (Real.arcosh_pos hx')).ne'
      have hsinh_cd : ContDiffAt ℝ ∞
          (fun y : 𝕄 => Real.sinh (Real.arcosh (-(η p y)))) x := by
        have hcomp := ContDiffAt.comp x Real.contDiff_sinh.contDiffAt harcosh
        simpa [Function.comp] using hcomp
      have hsecond : ContDiffAt ℝ ∞ (fun y : 𝕄 =>
          (Real.sinh (Real.arcosh (-(η p y))))⁻¹ • (y - (-(η p y)) • p)) x :=
        (hsinh_cd.inv hsinh_ne).smul
          (contDiffAt_id.sub (hu_cd.smul contDiffAt_const))
      exact (harcosh.prodMk hsecond).contDiffWithinAt
    · -- left inverse on the box
      rintro ⟨r, w⟩ ⟨hr, hw, hwn⟩
      have hr' : (0 : ℝ) < r := hr
      have h1 : -(η p (Real.cosh r • p + Real.sinh r • w)) = Real.cosh r := by
        rw [hηpx r w hw]
        ring
      have harc : Real.arcosh (Real.cosh r) = r := Real.arcosh_cosh hr'.le
      have hsinh_ne : Real.sinh r ≠ 0 := (Real.sinh_pos_iff.mpr hr').ne'
      refine Prod.ext ?_ ?_
      · show Real.arcosh (-(η p (Real.cosh r • p + Real.sinh r • w))) = r
        rw [h1, harc]
      · show (Real.sinh (Real.arcosh
            (-(η p (Real.cosh r • p + Real.sinh r • w)))))⁻¹
            • (Real.cosh r • p + Real.sinh r • w
              - (-(η p (Real.cosh r • p + Real.sinh r • w))) • p) = w
        rw [h1, harc]
        have hsub : Real.cosh r • p + Real.sinh r • w - Real.cosh r • p
            = Real.sinh r • w := by
          abel
        rw [hsub, smul_smul, inv_mul_cancel₀ hsinh_ne, one_smul]

/-- **Math.** Exercise 1.6.21 (4): **hyperbolas minimize**. Any curve on `Hⁿ`
from `p` to `q = p cosh r₀ + v₀ sinh r₀` has induced length
`∫ √η(ċ, ċ) ≥ r₀` (the integrand is the hyperbolic speed,
`hyperbolicSpace_metricInner`), with equality only on the hyperbola through
`p` and `q`. -/
theorem exercise1_6_21_minimize {p v₀ : 𝕄}
    (hp : η p p = -1) (hppos : 0 < p.2) (hv : η v₀ v₀ = 1) (hpv : η p v₀ = 0)
    {r₀ : ℝ} (hr : 0 < r₀) {c : ℝ → 𝕄} (hc : ContDiff ℝ ∞ c) {a b : ℝ}
    (hab : a ≤ b) (hH : ∀ t, η (c t) (c t) = -1 ∧ 0 < (c t).2)
    (hca : c a = p) (hcb : c b = Real.cosh r₀ • p + Real.sinh r₀ • v₀) :
    r₀ ≤ ∫ t in a..b, Real.sqrt (η (deriv c t) (deriv c t)) ∧
    ((∫ t in a..b, Real.sqrt (η (deriv c t) (deriv c t))) = r₀ →
      ∀ t ∈ Icc a b, ∃ s ∈ Icc 0 r₀,
        c t = Real.cosh s • p + Real.sinh s • v₀) := by
  have hderiv_cont : Continuous (deriv c) := hc.continuous_deriv (by simp)
  have hspeed_cont :
      Continuous fun t => Real.sqrt (η (deriv c t) (deriv c t)) :=
    Real.continuous_sqrt.comp
      (((minkowskiForm (EuclideanSpace ℝ (Fin n)) ℝ).continuous.comp
        hderiv_cont).clm_apply hderiv_cont)
  have hq_inner : -(η p (Real.cosh r₀ • p + Real.sinh r₀ • v₀))
      = Real.cosh r₀ := by
    rw [map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    rw [hp, hpv]
    ring
  -- part (1): comparison with the (mollified) radial coordinate
  have h1 : r₀ ≤ ∫ t in a..b, Real.sqrt (η (deriv c t) (deriv c t)) := by
    have h := arcosh_neg_minkowskiForm_le_length hc hab hH
    rw [hca, hcb, hq_inner] at h
    rwa [Real.arcosh_cosh hr.le] at h
  refine ⟨h1, fun heq t ht => ?_⟩
  -- part (2): equality — split the length at `t` and use the equality case
  -- of the hyperbolic triangle inequality
  have hsplit : (∫ s in a..t, Real.sqrt (η (deriv c s) (deriv c s)))
      + ∫ s in t..b, Real.sqrt (η (deriv c s) (deriv c s))
      = ∫ s in a..b, Real.sqrt (η (deriv c s) (deriv c s)) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hspeed_cont.intervalIntegrable a t)
      (hspeed_cont.intervalIntegrable t b)
  have h2 := arcosh_neg_minkowskiForm_le_length hc ht.1 hH
  have h3 := arcosh_neg_minkowskiForm_le_length hc ht.2 hH
  rw [hca] at h2
  rw [hcb] at h3
  have hsum : Real.arcosh (-(η p (c t)))
      + Real.arcosh (-(η (c t)
          (Real.cosh r₀ • p + Real.sinh r₀ • v₀))) ≤ r₀ := by
    linarith [h2, h3, hsplit, heq]
  obtain ⟨hs_mem, hs_eq⟩ := eq_hyperbola_of_arcosh_add_arcosh_le hp hppos hv
    hpv hr (hH t).1 (hH t).2 hsum
  exact ⟨Real.arcosh (-(η p (c t))), hs_mem, hs_eq⟩

/-- **Math.** Exercise 1.6.21 (5): there is no Riemannian immersion from an
open subset of `ℝⁿ` into `Hⁿ` (`n ≥ 2`), stated pointwise on the open set as
in `exercise1_6_20_no_immersion`, against the hyperbolic metric
`hyperbolicSpace n 1`.

Proved by `no_isometricImmersion_flat_to_hyperboloid`: the same second-order
computation as for the sphere, run with the Minkowski form in place of the
inner product.  The ambient form's signature never enters — only the fact
that the normal `ι ∘ F` has nonzero square (`η = -1` here, `⟪·,·⟫ = 1` there),
so hyperbolic space is as rigid as the sphere against flat immersions. -/
theorem exercise1_6_21_no_immersion (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hne : U.Nonempty)
    (F : EuclideanSpace ℝ (Fin n) → hyperboloid n 1)
    (hFd : ∀ x ∈ U, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ F x)
    (hFinj : ∀ x ∈ U, Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F x))
    (hFiso : ∀ x ∈ U, ∀ u v : EuclideanSpace ℝ (Fin n),
      ⟪u, v⟫_ℝ = (hyperbolicSpace n 1).metricInner (F x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F x u)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F x v)) :
    False :=
  no_isometricImmersion_flat_to_hyperboloid hn hU hne F hFd hFiso

/-- **Math.** **Exercise 1.6.21** (Petersen §1.6): geometry of hyperbolic
space `Hⁿ ⊂ ℝ^{n,1}` (ambient Minkowski formulation; the induced metric is
`hyperbolicSpace`):

1. hyperbolas `p cosh t + v sinh t` are unit-speed curves on `Hⁿ`
   (`exercise1_6_21_hyperbola`);
2. `F(r, v) = p cosh r + v sinh r` is a diffeomorphism
   `(0, ∞) × S^{n-1} → Hⁿ − {p}` (`exercise1_6_21_polar`);
3. the radial field is
   `∂_r|_q = (−p − (q⋅p)q)/√(−1 + (q⋅p)²) = p sinh r₀ + v₀ cosh r₀`
   (`exercise1_6_21_radialField`);
4. every curve from `p` to `q = F(r₀, v₀)` has length `≥ r₀`, with equality
   only on the hyperbola (`exercise1_6_21_minimize`);
5. no open `U ⊂ ℝⁿ` immerses isometrically into `Hⁿ` for `n ≥ 2`
   (`exercise1_6_21_no_immersion`). -/
theorem exercise1_6_21 (hn : 2 ≤ n) {p v₀ : 𝕄}
    (hp : η p p = -1) (hppos : 0 < p.2) (hv : η v₀ v₀ = 1) (hpv : η p v₀ = 0)
    {r₀ : ℝ} (hr : 0 < r₀) :
    ((∀ t, η (Real.cosh t • p + Real.sinh t • v₀)
        (Real.cosh t • p + Real.sinh t • v₀) = -1) ∧
      (∀ t, 0 < (Real.cosh t • p + Real.sinh t • v₀).2) ∧
      Real.cosh 0 • p + Real.sinh 0 • v₀ = p ∧
      deriv (fun s => Real.cosh s • p + Real.sinh s • v₀) 0 = v₀ ∧
      (∀ t, η (deriv (fun s => Real.cosh s • p + Real.sinh s • v₀) t)
        (deriv (fun s => Real.cosh s • p + Real.sinh s • v₀) t) = 1)) ∧
    Set.BijOn (fun q : ℝ × 𝕄 => Real.cosh q.1 • p + Real.sinh q.1 • q.2)
      (Ioi 0 ×ˢ {w : 𝕄 | η p w = 0 ∧ η w w = 1})
      {x : 𝕄 | η x x = -1 ∧ 0 < x.2 ∧ x ≠ p} ∧
    ((Real.sqrt (-1 + (η (Real.cosh r₀ • p + Real.sinh r₀ • v₀) p) ^ 2))⁻¹ •
        (-p - (η (Real.cosh r₀ • p + Real.sinh r₀ • v₀) p) •
          (Real.cosh r₀ • p + Real.sinh r₀ • v₀))
      = Real.sinh r₀ • p + Real.cosh r₀ • v₀) ∧
    (∀ (c : ℝ → 𝕄), ContDiff ℝ ∞ c → ∀ (a b : ℝ), a ≤ b →
      (∀ t, η (c t) (c t) = -1 ∧ 0 < (c t).2) → c a = p →
      c b = Real.cosh r₀ • p + Real.sinh r₀ • v₀ →
      r₀ ≤ ∫ t in a..b, Real.sqrt (η (deriv c t) (deriv c t))) ∧
    (∀ (U : Set (EuclideanSpace ℝ (Fin n))), IsOpen U → U.Nonempty →
      ∀ F : EuclideanSpace ℝ (Fin n) → hyperboloid n 1,
      (∀ x ∈ U, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ F x) →
      (∀ x ∈ U, Function.Injective
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F x)) →
      (∀ x ∈ U, ∀ u v : EuclideanSpace ℝ (Fin n),
        ⟪u, v⟫_ℝ = (hyperbolicSpace n 1).metricInner (F x)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F x u)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F x v)) →
      False) := by
  obtain ⟨h1, h2, h3, _, h5, h6⟩ := exercise1_6_21_hyperbola hp hppos hv hpv
  refine ⟨⟨h1, h2, h3, h5, h6⟩, (exercise1_6_21_polar hp hppos).2.1, ?_, ?_, ?_⟩
  · exact (exercise1_6_21_radialField hp hv hpv hr).2
  · intro c hc a b hab hH hca hcb
    exact (exercise1_6_21_minimize hp hppos hv hpv hr hc hab hH hca hcb).1
  · intro U hU hne F hFd hFinj hFiso
    exact exercise1_6_21_no_immersion hn hU hne F hFd hFinj hFiso

end Exercise21

end PetersenLib

end
